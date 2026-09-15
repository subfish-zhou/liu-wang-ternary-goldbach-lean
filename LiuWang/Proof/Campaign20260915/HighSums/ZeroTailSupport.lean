import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Height

set_option autoImplicit false
noncomputable section

open MeasureTheory
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.HighSum
open LiuWang.Proof.SourceRoute.HighSum.Continuation
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.Campaign20260915.HighSums

theorem near_one_count_zero_of_not_first {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y lam : ℝ}
    (hy : omegaCutoff N q ≤ y) (hc : ¬ FirstCase q y) (hlam : lam ≤ 0.12) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y = 0 := by
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have : IsEmpty (ClosedSlots q (1 - lam / Real.log ((q : ℝ) * y)) y) :=
    ⟨fun p => hc ⟨fullSlot p, (closedSlot_gap_le hs p).trans hlam⟩⟩
  rw [← card_closedSlots, Fintype.card_of_isEmpty]

theorem tail_slice_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    0 ≤ lambdaCountSegment N q y 0 (1 / c1) := by
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 ≤ Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  unfold lambdaCountSegment
  apply mul_nonneg (div_nonneg hL hs)
  apply intervalIntegral.integral_nonneg_of_forall c1_bounds.1.le
  intro lam
  unfold lambdaCountIntegrand
  positivity

theorem tail_slice_zero_of_not_first {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y)
    (hc : ¬ FirstCase q y) :
    lambdaCountSegment N q y 0 (1 / c1) = 0 := by
  unfold lambdaCountSegment
  have he : (∫ lam in (0 : ℝ)..(1 / c1), lambdaCountIntegrand N q y lam) = 0 := by
    calc
      _ = ∫ _lam in (0 : ℝ)..(1 / c1), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        rw [Set.uIcc_of_le c1_bounds.1.le] at hlam
        unfold lambdaCountIntegrand
        rw [near_one_count_zero_of_not_first hN hy hc
          (hlam.2.trans c1_bounds.2.1.le), Nat.cast_zero, mul_zero]
      _ = 0 := by simp
  rw [he, mul_zero]

theorem tail_slice_zero_of_second {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hc : SecondCase q y) :
    lambdaCountSegment N q y 0 (1 / c1) = 0 := by
  unfold lambdaCountSegment
  have he : (∫ lam in (0 : ℝ)..(1 / c1), lambdaCountIntegrand N q y lam) = 0 := by
    calc
      _ = ∫ _lam in (0 : ℝ)..(1 / c1), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        rw [Set.uIcc_of_le c1_bounds.1.le] at hlam
        unfold lambdaCountIntegrand
        rw [actual_second_exclusion hN hq hy hc
          (hlam.2.trans c1_bounds.2.1.le), Nat.cast_zero, mul_zero]
      _ = 0 := by simp
  rw [he, mul_zero]

theorem zeroTail_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0 ≤ zeroTail N q := by
  apply intervalIntegral.integral_nonneg (WeightedLowZeros.omegaCutoff_le_sourceT hN)
  intro y hy
  exact mul_nonneg (by unfold heightKernel; positivity) (tail_slice_nonneg hN hy.1)

theorem zeroTail_eq_first_case_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    zeroTail N q =
      ∫ y in omegaCutoff N q..sourceT N,
        if FirstCase q y then heightKernel y * lambdaCountSegment N q y 0 (1 / c1)
        else 0 := by
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)] at hy
  dsimp only
  by_cases hc : FirstCase q y
  · simp only [if_pos hc]
  · rw [if_neg hc, tail_slice_zero_of_not_first hN hy.1 hc, mul_zero]

theorem zeroTail_zero_of_second {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    zeroTail N q = 0 := by
  calc
    _ = ∫ _y in omegaCutoff N q..sourceT N, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)] at hy
      dsimp only
      rw [tail_slice_zero_of_second hN hq hy.1 (hcase y hy), mul_zero]
    _ = 0 := by simp

theorem tail_slice_le_two_segments {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    lambdaCountSegment N q y 0 (1 / c1) ≤
      2 * lambdaSegment (sourceL N) (Real.log ((q : ℝ) * y)) 0 (1 / c1) := by
  by_cases hc : FirstCase q y
  · apply countSegment_le_cap hN hy le_rfl c1_bounds.1.le
      (by linarith [c1_bounds.2.1])
    intro lam hlam
    exact_mod_cast actual_first_count hN hq hy hc
      (show lam ≤ 0.3221 by linarith [hlam.2, c1_bounds.2.1])
  · rw [tail_slice_zero_of_not_first hN hy hc]
    have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
    have hs : 0 < Real.log ((q : ℝ) * y) := by
      linarith [original_log_product_ge_ten hN hy]
    exact mul_nonneg (by norm_num) (segment_nonneg hL hs c1_bounds.1.le)

#print axioms near_one_count_zero_of_not_first
#print axioms zeroTail_eq_first_case_integral
#print axioms zeroTail_zero_of_second
#print axioms tail_slice_le_two_segments

end LiuWang.Proof.Campaign20260915.HighSums
