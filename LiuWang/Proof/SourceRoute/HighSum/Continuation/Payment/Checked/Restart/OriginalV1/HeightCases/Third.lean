import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.Classification

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.NearOneDensity
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases

def thirdTableEnvelope (L s : ℝ) : ℝ :=
  2 * lambdaSegment L s 0.15 0.2067 +
    4 * lambdaSegment L s 0.2067 0.26213 +
    7 * lambdaSegment L s 0.26213 0.27 +
    8 * lambdaSegment L s 0.27 0.28 +
    9 * lambdaSegment L s 0.28 0.3 +
    10 * lambdaSegment L s 0.3 0.31 +
    11 * lambdaSegment L s 0.31 0.32 +
    13 * lambdaSegment L s 0.32 0.33 +
    20 * lambdaSegment L s 0.33 0.36

/-- A new telescoping bridge from the tables, not a reading of the missing operator in (2.37). -/
theorem third_table_bridge {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    thirdTableEnvelope L s =
      2 * Real.exp (-0.15 * L / s) + 2 * Real.exp (-0.2067 * L / s) +
      3 * Real.exp (-0.26213 * L / s) + Real.exp (-0.27 * L / s) +
      Real.exp (-0.28 * L / s) + Real.exp (-0.3 * L / s) +
      Real.exp (-0.31 * L / s) + 2 * Real.exp (-0.32 * L / s) +
      7 * Real.exp (-0.33 * L / s) - 20 * Real.exp (-0.36 * L / s) := by
  unfold thirdTableEnvelope
  simp only [lambdaSegment_eq hL hs]
  ring

theorem third_lower_segment_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ}
    (hy : omegaCutoff N q ≤ y) (hc : ThirdCase q y) :
    lambdaCountSegment N q y (1 / c1) 0.15 = 0 := by
  unfold lambdaCountSegment
  have he : (∫ lam in (1 / c1)..(0.15 : ℝ), lambdaCountIntegrand N q y lam) = 0 := by
    calc
      _ = ∫ _lam in (1 / c1)..(0.15 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro lam hlam
        rw [Set.uIcc_of_le (show 1 / c1 ≤ 0.15 by linarith [c1_bounds.2.1])] at hlam
        unfold lambdaCountIntegrand
        rw [third_closed_count_zero hN hy hc hlam.2, Nat.cast_zero, mul_zero]
      _ = 0 := by simp
  rw [he, mul_zero]

theorem actual_third_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hc : ThirdCase q y)
    (hT1 : strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4) :
    lambdaCountSegment N q y (1 / c1) 0.36 ≤
      thirdTableEnvelope (sourceL N) (Real.log ((q : ℝ) * y)) := by
  have h1 := countSegment_le_strict_gate hN hy (by norm_num : (0 : ℝ) ≤ 0.15)
    (by norm_num : (0.15 : ℝ) ≤ 0.2067) (by norm_num)
    (actual_T2_strict_count hN hq hy)
  have h2 := countSegment_le_strict_gate hN hy (by norm_num : (0 : ℝ) ≤ 0.2067)
    (by norm_num : (0.2067 : ℝ) ≤ 0.26213) (by norm_num) hT1
  have h3 := lambdaCountSegment_le_row .r027 hN hq hy (a := 0.26213) (b := 0.27)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h4 := lambdaCountSegment_le_row .r028 hN hq hy (a := 0.27) (b := 0.28)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h5 := lambdaCountSegment_le_row .r030 hN hq hy (a := 0.28) (b := 0.3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h6 := lambdaCountSegment_le_row .r031 hN hq hy (a := 0.3) (b := 0.31)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h7 := lambdaCountSegment_le_row .r032 hN hq hy (a := 0.31) (b := 0.32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h8 := lambdaCountSegment_le_row .r033 hN hq hy (a := 0.32) (b := 0.33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  have h9 := lambdaCountSegment_le_row .r036 hN hq hy (a := 0.33) (b := 0.36)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowLambda])
  norm_num [rowBound, rowMultiplicity, rowSelectedBound] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [countSegment_add hN hy c1_bounds.1.le (show 1 / c1 ≤ 0.15 by linarith [c1_bounds.2.1])
      (by norm_num : (0.15 : ℝ) ≤ 0.36) (by norm_num),
    third_lower_segment_zero hN hy hc, zero_add]
  have hsplit {a b d : ℝ} := @countSegment_add N q _ hN y a b d hy
  rw [hsplit (by norm_num : (0 : ℝ) ≤ 0.15) (by norm_num : (0.15 : ℝ) ≤ 0.2067)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.2067) (by norm_num : (0.2067 : ℝ) ≤ 0.26213)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.26213) (by norm_num : (0.26213 : ℝ) ≤ 0.27)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.27) (by norm_num : (0.27 : ℝ) ≤ 0.28)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.28) (by norm_num : (0.28 : ℝ) ≤ 0.3)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.3) (by norm_num : (0.3 : ℝ) ≤ 0.31)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.31) (by norm_num : (0.31 : ℝ) ≤ 0.32)
      (by norm_num) (by norm_num),
    hsplit (by norm_num : (0 : ℝ) ≤ 0.32) (by norm_num : (0.32 : ℝ) ≤ 0.33)
      (by norm_num) (by norm_num)]
  unfold thirdTableEnvelope
  linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases
