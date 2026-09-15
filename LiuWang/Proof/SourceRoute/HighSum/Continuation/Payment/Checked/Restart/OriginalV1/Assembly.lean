import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.EndpointPayment
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Consumer
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Outcome

/-! Reuse the frozen signed (2.32) certificate after paying the T endpoint.

The remaining ranges are printed explicitly. In particular, the lambda
lower endpoint is still zero: the source-check truncation in (2.23) is not
silently supplied by this assembly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1

theorem source21_source32_excess_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y) :
    excessHighSum N q ≤ (18 / 100000000000 : ℝ) / sourceL N ^ (4 : ℕ) +
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ((∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
          layerKernel N alpha * (familyCount q alpha y : ℝ)) +
          lambdaCountSegment N q y 0 0.36)) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have he :
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y * unpaidAlpha N q y) =
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ((∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
          layerKernel N alpha * (familyCount q alpha y : ℝ)) +
          lambdaCountSegment N q y 0 0.36) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)] at hy
    dsimp only
    rw [unpaidAlpha_eq_original_ranges hN hy.1]
  have h := source21_excess_reduction hN hq hT7
  rw [original_height_eq_unpaid_add_table hN hq, he] at h
  linarith [Checked.actual_source32 hN hq]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
