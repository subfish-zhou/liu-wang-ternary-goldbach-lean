import LiuWang.Proof.SourceRoute.HighSum.SourceParameters
import LiuWang.Proof.SourceRoute.HighSum.Continuation.EndpointScalar

/-! # The original directed denominator and logarithm comparisons in (2.26) -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

def source26AlphaEnvelope (L s : ℝ) : ℝ :=
  (17102 + 254231 / s) * s ^ (6 : ℕ) * L / (L - 4 * s) *
    Real.exp (-0.478 * (L - 4 * s) / s) +
  16541 * s ^ (6 : ℕ) * Real.exp (-0.478 * L / s)

theorem source26_denominator {L s : ℝ} (hL : 3100 ≤ L)
    (hs : s ≤ 18 * Real.log L) : 0 < L - 4 * s := by
  linarith [log_le_original_linear hL]

theorem original_density_denominator_compare {N q : ℕ} [NeZero q]
    {y : ℝ} (hy : 0 < y) :
    sourceL N - 4 * Real.log ((q : ℝ) * y) ≤
      sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (NeZero.pos q))
  rw [Real.log_mul hq0.ne' hy.ne',
    Real.log_mul (pow_pos hq0 _).ne' (pow_pos hy _).ne', Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem original_log_product_upper {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : 0 < y) (hyT : y ≤ sourceT N) :
    Real.log ((q : ℝ) * y) ≤ 18 * Real.log (sourceL N) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hp := mul_le_mul hq hyT hy.le (show 0 ≤ sourceP N by unfold sourceP; positivity)
  have h := Real.log_le_log (mul_pos hq0 hy) hp
  change Real.log ((q : ℝ) * y) ≤ Real.log (sourceL N ^ (3 : ℕ) * sourceL N ^ (15 : ℕ)) at h
  rw [Real.log_mul (pow_pos hL _).ne' (pow_pos hL _).ne', Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem source24_to_source26 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hyT : y ≤ sourceT N) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * Applications.sourceSevenBound q alpha y) ≤
      source26AlphaEnvelope (sourceL N) (Real.log ((q : ℝ) * y)) := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hn1 : 1 < (N : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 3100)).trans_le hN
  have hy1 : 1 ≤ y := by linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hy0 : 0 < y := by linarith
  have hs := original_log_product_ge_ten hN hy
  have hs0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hd := source26_denominator hL (original_log_product_upper hN hq hy0 hyT)
  have hD := original_density_denominator_compare (N := N) (q := q) hy0
  have hh := sourceSeven_integral_le_source24 hn1 hy0 (by linarith)
    (hd.trans_le hD) (original_alpha_cutoff_mem hN hy).1
  have hc : 0 ≤ (17102 + 254231 / Real.log ((q : ℝ) * y)) *
      Real.log ((q : ℝ) * y) ^ (6 : ℕ) * sourceL N := by positivity
  have hdiv := div_le_div_of_nonneg_left hc hd hD
  have hexp : Real.exp (-0.478 *
      (sourceL N - Real.log ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ))) /
      Real.log ((q : ℝ) * y)) ≤ Real.exp (-0.478 *
      (sourceL N - 4 * Real.log ((q : ℝ) * y)) / Real.log ((q : ℝ) * y)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hs0.le
    linarith
  have hmain := mul_le_mul hdiv hexp (Real.exp_pos _).le (by positivity)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hlogs := Real.log_le_log hy0
    (show y ≤ (q : ℝ) * y by nlinarith)
  have hp := pow_le_pow_left₀ (Real.log_nonneg hy1) hlogs 6
  have hlast := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ 16541 * Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) by positivity)
  unfold source26AlphaEnvelope
  nlinarith only [hh, hmain, hlast]

theorem source26_normalization (L s : ℝ) :
    L ^ (4 : ℕ) * Real.exp (-s) * source26AlphaEnvelope L s =
      Real.exp (-s) *
        ((17102 + 254231 / s) * s ^ (6 : ℕ) * L ^ (5 : ℕ) / (L - 4 * s) *
          Real.exp (-0.478 * (L - 4 * s) / s) +
        16541 * s ^ (6 : ℕ) * L ^ (4 : ℕ) * Real.exp (-0.478 * L / s)) := by
  unfold source26AlphaEnvelope
  ring

theorem original_source26_integrable {L : ℝ} (hL : 3100 ≤ L) :
    IntervalIntegrable (fun s => L ^ (4 : ℕ) * Real.exp (-s) * source26AlphaEnvelope L s)
      volume (Real.log (3.36 * L ^ (3 : ℕ))) (Real.log (L ^ (18 : ℕ))) := by
  have h0 : 0 < L := by linarith
  have hlog := original_log_linear hL
  have hA : 0 < Real.log (3.36 * L ^ (3 : ℕ)) := by
    apply Real.log_pos
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
    nlinarith
  have hab : Real.log (3.36 * L ^ (3 : ℕ)) ≤ Real.log (L ^ (18 : ℕ)) := by
    rw [Real.log_mul (by norm_num) (pow_pos h0 _).ne', Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3.36)
    linarith
  have hs (s : ℝ) (hs : s ∈ Set.uIcc (Real.log (3.36 * L ^ (3 : ℕ))) (Real.log (L ^ (18 : ℕ)))) :
      s ≠ 0 ∧ L - 4 * s ≠ 0 := by
    rw [Set.uIcc_of_le hab] at hs
    have hu : s ≤ 18 * Real.log L := by simpa only [Real.log_pow, Nat.cast_ofNat] using hs.2
    exact ⟨ne_of_gt (hA.trans_le hs.1), (source26_denominator hL hu).ne'⟩
  apply ContinuousOn.intervalIntegrable
  unfold source26AlphaEnvelope
  have hs0 := fun s h => (hs s h).1
  have hd0 := fun s h => (hs s h).2
  fun_prop

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
