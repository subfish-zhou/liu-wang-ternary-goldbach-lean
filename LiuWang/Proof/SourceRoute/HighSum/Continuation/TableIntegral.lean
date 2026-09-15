import LiuWang.Proof.SourceRoute.HighSum.LambdaSegments
import LiuWang.Proof.NearOneDensity.Continuation.CountInterface

/-! # Actual family-count payment of the seven source lambda segments -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation
open LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation

def lambdaCountIntegrand (N q : ℕ) [NeZero q] (y lam : ℝ) : ℝ :=
  (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
    (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ)

def lambdaCountSegment (N q : ℕ) [NeZero q] (y a b : ℝ) : ℝ :=
  sourceL N / Real.log ((q : ℝ) * y) *
    ∫ lam in a..b, lambdaCountIntegrand N q y lam

def source31Profile (L s : ℝ) : ℝ :=
  35 * Real.exp (-0.36 * L / s) + 54 * Real.exp (-0.39 * L / s) +
  93 * Real.exp (-0.42 * L / s) + 110 * Real.exp (-0.45 * L / s) +
  372 * Real.exp (-0.46 * L / s) + 1004 * Real.exp (-0.47 * L / s) +
  12332 * Real.exp (-0.475 * L / s) - 14000 * Real.exp (-0.478 * L / s)

theorem original_table_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    1 ≤ y ∧ 100000000000 ≤ (q : ℝ) * y ∧
      (q : ℝ) * max 1 y ≤ (q : ℝ) * y := by
  have hy1 : 1 ≤ y := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  exact ⟨hy1, original_product_ge hN hy, by rw [max_eq_right hy1]⟩

theorem original_familyCount_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y lam : ℝ} (hy : omegaCutoff N q ≤ y) (hlam : lam ≤ rowLambda r) :
    (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ) ≤ rowBound r := by
  have hd := original_table_domain hN hq hy
  have hs : 0 ≤ Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  exact_mod_cast NearOneDensity.Continuation.familyCount_row_tail r hd.2.1 hd.2.2
    (sub_le_sub_left (div_le_div_of_nonneg_right hlam hs) 1)

theorem lambdaCountIntegrand_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a b : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478) :
    IntervalIntegrable (lambdaCountIntegrand N q y) volume a b := by
  apply (original_source30_integrable hN hy (a := 0) le_rfl (by norm_num)).mono_set
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 0.478)]
  exact Set.Icc_subset_Icc ha hb

theorem lambdaCountSegment_le_row (r : DensityRow) {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y a b : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478) (hr : b ≤ rowLambda r) :
    lambdaCountSegment N q y a b ≤
      (rowBound r : ℝ) * lambdaSegment (sourceL N) (Real.log ((q : ℝ) * y)) a b := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr hn
  have hn0' : (N : ℝ) ≠ 0 := hn0.ne'
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have hi : IntervalIntegrable
      (fun lam => (rowBound r : ℝ) * (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)))
      volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on hab
    (lambdaCountIntegrand_integrable hN hy ha hab hb) hi (fun lam hlam => by
      unfold lambdaCountIntegrand
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (original_familyCount_row r hN hq hy (hlam.2.trans hr))
        (Real.rpow_nonneg hn0.le _))
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hh := mul_le_mul_of_nonneg_left h (div_nonneg hL hs.le)
  rw [intervalIntegral.integral_const_mul] at hh
  rw [lambdaSegment_eq_source_power hn]
  exact hh.trans_eq (by ring)

theorem lambdaCountSegment_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    lambdaCountSegment N q y 0.36 0.478 =
      lambdaCountSegment N q y 0.36 0.39 +
      lambdaCountSegment N q y 0.39 0.42 +
      lambdaCountSegment N q y 0.42 0.45 +
      lambdaCountSegment N q y 0.45 0.46 +
      lambdaCountSegment N q y 0.46 0.47 +
      lambdaCountSegment N q y 0.47 0.475 +
      lambdaCountSegment N q y 0.475 0.478 := by
  have h := original_source30 hN hy (a := 0.36) (by norm_num) le_rfl
  dsimp only at h
  simp only [intervalIntegral.integral_same, zero_add] at h
  unfold lambdaCountSegment lambdaCountIntegrand
  rw [h]
  ring

theorem actual_source31_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    lambdaCountSegment N q y 0.36 0.478 ≤
      source31Profile (sourceL N) (Real.log ((q : ℝ) * y)) := by
  have h1 := lambdaCountSegment_le_row .r039 hN hq hy
    (a := 0.36) (b := 0.39) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  have h2 := lambdaCountSegment_le_row .r042 hN hq hy
    (a := 0.39) (b := 0.42) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  have h3 := lambdaCountSegment_le_row .r045 hN hq hy
    (a := 0.42) (b := 0.45) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  have h4 := lambdaCountSegment_le_row .r046 hN hq hy
    (a := 0.45) (b := 0.46) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  have h5 := lambdaCountSegment_le_row .r047 hN hq hy
    (a := 0.46) (b := 0.47) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  have h6 := lambdaCountSegment_le_row .r0475 hN hq hy
    (a := 0.47) (b := 0.475) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  have h7 := lambdaCountSegment_le_row .r0478 hN hq hy
    (a := 0.475) (b := 0.478) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [rowLambda])
  norm_num [rowBound, rowMultiplicity, rowSelectedBound] at h1 h2 h3 h4 h5 h6 h7
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  rw [lambdaCountSegment_split hN hy, source31Profile, ← source31_signed_segments hL hs]
  norm_num only [OfScientific.ofScientific]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add h1 h2) h3) h4) h5) h6) h7

theorem actual_source31_alpha_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * y))..
        (1 - 0.36 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
        source31Profile (sourceL N) (Real.log ((q : ℝ) * y)) := by
  rw [actual_lambda_substitution]
  exact actual_source31_slice hN hq hy

end LiuWang.Proof.SourceRoute.HighSum.Continuation
