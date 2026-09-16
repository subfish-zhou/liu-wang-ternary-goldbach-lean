import LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator.CutoffIntervals
import LiuWang.Proof.Campaign20260915.ZetaValidation.OriginalPhaseCenter
import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.SourceSums

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open Finset

def originalCache : ℕ → SharedEntry := makeEntry (10 ^ 24) 80

def originalMainCenter : ℚ :=
  evaluate (10 ^ 24) originalCache 1894438 originalHeightGammaArgumentCenter 549

def originalMainRadius : ℚ :=
  evaluationRadius (10 ^ 24) originalCache 1894438 0 (1 / 1000000) 549

noncomputable section

theorem finiteMainSum_eq_sourceRealMainSum (t : ℝ) (m : ℕ) :
    finiteMainSum t m = sourceRealMainSum t m := by
  simp only [finiteMainSum, sourceRealMainSum, mul_sum]
  apply sum_congr rfl
  intro j _
  simp only [sourceTerm, Nat.cast_add, Nat.cast_one]
  have hc : Real.cos (criticalGammaArgument t - t * Real.log (j + 1)) =
      Real.cos (t * Real.log (j + 1) - criticalGammaArgument t) := by
    rw [← Real.cos_neg (t * Real.log (j + 1) - criticalGammaArgument t)]
    congr 1
    ring
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← one_div, hc]
  ring

theorem reciprocalSqrt_width {D n : ℕ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    (reciprocalSqrtUpper n D : ℝ) - (reciprocalSqrtLower n D : ℝ) ≤ 1 / (D : ℝ) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hkN : D ≤ Nat.sqrt (n * D ^ 2) :=
    Nat.le_sqrt'.mpr (by nlinarith [Nat.mul_le_mul_right (D ^ 2) hn])
  have hk : (D : ℝ) ≤ Nat.sqrt (n * D ^ 2) := by exact_mod_cast hkN
  have hkp : (0 : ℝ) < Nat.sqrt (n * D ^ 2) := hDp.trans_le hk
  unfold reciprocalSqrtUpper reciprocalSqrtLower
  push_cast
  apply (le_div_iff₀ hDp).mpr
  have he : ((D : ℝ) / Nat.sqrt (n * D ^ 2) -
      (D : ℝ) / (Nat.sqrt (n * D ^ 2) + 1)) * D =
      (D : ℝ) ^ 2 / (Nat.sqrt (n * D ^ 2) * (Nat.sqrt (n * D ^ 2) + 1)) := by
    field_simp
    ring
  rw [he, div_le_one (by positivity)]
  nlinarith

theorem originalCache_logRadius {n : ℕ} (hn : n ≤ 550) :
    ((originalCache n).logRadius : ℝ) ≤ 1 / (10 : ℝ) ^ 20 := by
  have hk : logExponent n ≤ 551 := by
    have h := Nat.log_le_self 2 n
    rw [logExponent, Nat.log2_eq_log_two]
    omega
  have hkR : (logExponent n : ℝ) ≤ 551 := by exact_mod_cast hk
  dsimp [originalCache, makeEntry]
  push_cast
  norm_num
  linarith

theorem originalCache_phaseFits {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 550) :
    PhaseFits (originalCache n) 1894438 originalHeightGammaArgumentCenter := by
  have he := makeEntry_valid (D := 10 ^ 24) (by norm_num) hn 80
  change EntryValid n (originalCache n) at he
  have hln0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hln : Real.log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))
    linarith
  have hlog : |((originalCache n).logCenter : ℝ)| ≤ 551 := by
    have h := abs_sub_le ((originalCache n).logCenter : ℝ) (Real.log (n : ℝ)) 0
    rw [sub_zero, sub_zero, abs_sub_comm, abs_of_nonneg hln0] at h
    have hnR : (n : ℝ) ≤ 550 := by exact_mod_cast hN
    linarith [he.1, originalCache_logRadius hN]
  have ha := abs_sub_le ((1894438 : ℝ) * ((originalCache n).logCenter : ℝ)) 0
    (originalHeightGammaArgumentCenter : ℝ)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1894438)] at ha
  have hr := roundRationalAt_error (D := 10 ^ 24) (by norm_num)
    (1894438 * (originalCache n).logCenter - originalHeightGammaArgumentCenter)
  have htri := abs_sub_le
    (phaseArgument (originalCache n) 1894438 originalHeightGammaArgumentCenter : ℝ)
    ((1894438 * (originalCache n).logCenter - originalHeightGammaArgumentCenter : ℚ) : ℝ) 0
  simp only [sub_zero] at htri
  change |(phaseArgument (originalCache n) 1894438 originalHeightGammaArgumentCenter : ℝ) -
    ((1894438 * (originalCache n).logCenter - originalHeightGammaArgumentCenter : ℚ) : ℝ)| ≤ _ at hr
  have hb : |(phaseArgument (originalCache n) 1894438 originalHeightGammaArgumentCenter : ℝ)| ≤
      (2 : ℝ) ^ 32 := by
    push_cast at htri hr
    norm_num at hr ⊢
    linarith [originalHeightGammaArgumentCenter_abs]
  have hbQ : |phaseArgument (originalCache n) 1894438 originalHeightGammaArgumentCenter| ≤
      (2 : ℚ) ^ 32 := by exact_mod_cast hb
  unfold PhaseFits
  rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ 32),
    div_le_one (by positivity)]
  exact hbQ

theorem originalHeight_cutoff : sourceCutoff 1894438 = 549 := by
  apply cutoffWindow_constant (a := 1894438) (b := 1894438)
  · norm_num [CutoffWindow, piLower, piUpper, rationalPi20]
  · norm_num

theorem originalMainRadius_le : (originalMainRadius : ℝ) ≤ 1 / 500 := by
  have hterm (j : ℕ) (hj : j ∈ range 549) :
      ((termRadius (originalCache (j + 1)) 1894438 0 (1 / 1000000) + 1 / 10 ^ 24 : ℚ) : ℝ) ≤
        1 / 400000 := by
    have hn : j + 1 ≤ 550 := by simp only [mem_range] at hj; omega
    have he := makeEntry_valid (D := 10 ^ 24) (by norm_num) (n := j + 1) (by omega) 80
    change EntryValid (j + 1) (originalCache (j + 1)) at he
    have hl := originalCache_logRadius hn
    have hw : ((originalCache (j + 1)).weightRadius : ℝ) ≤ 1 / ((10 ^ 24 : ℕ) : ℝ) := by
      simpa only [originalCache, makeEntry, Rat.cast_sub] using
        reciprocalSqrt_width (D := 10 ^ 24) (n := j + 1) (by norm_num) (by omega)
    have hrad0 : (0 : ℝ) ≤ (originalCache (j + 1)).logRadius := (abs_nonneg _).trans he.1
    have hp := mul_le_mul_of_nonneg_left he.2.2.1
      (show 0 ≤ 1894438 * ((originalCache (j + 1)).logRadius : ℝ) +
        1 / 1000000 + 2 / 10 ^ 24 by positivity)
    dsimp [termRadius]
    push_cast
    norm_num at hw hp ⊢
    nlinarith
  have hsum := sum_le_sum hterm
  change (∑ j ∈ range 549,
    ((termRadius (originalCache (j + 1)) 1894438 0 (1 / 1000000) + 1 / 10 ^ 24 : ℚ) : ℝ)) ≤
      ∑ _j ∈ range 549, (1 / 400000 : ℝ) at hsum
  have hid : (originalMainRadius : ℝ) = ∑ j ∈ range 549,
      ((termRadius (originalCache (j + 1)) 1894438 0 (1 / 1000000) + 1 / 10 ^ 24 : ℚ) : ℝ) := by
    norm_num [originalMainRadius, evaluationRadius]
  rw [hid]
  exact hsum.trans (by norm_num)

theorem originalMainCenter_error :
    |sourceMainSum 1894438 - (originalMainCenter : ℝ)| ≤ (originalMainRadius : ℝ) := by
  rw [sourceMainSum, originalHeight_cutoff]
  exact makeEntry_evaluate_error (by norm_num) (by norm_num)
    (t := 1894438) (dt := 0) (by norm_num)
    (by simpa using originalHeightGammaArgumentCenter_error)
    (fun n hn hN => originalCache_phaseFits hn (by omega))

theorem original_source_main_enclosure :
    |sourceRealMainSum 1894438 549 - (originalMainCenter : ℝ)| ≤ 1 / 500 := by
  have h := originalMainCenter_error.trans originalMainRadius_le
  simpa [sourceMainSum, originalHeight_cutoff, finiteMainSum_eq_sourceRealMainSum] using h

#print axioms finiteMainSum_eq_sourceRealMainSum
#print axioms original_source_main_enclosure

end

end LiuWang.Proof.Campaign20260915.ZetaMainSumEvaluator
