import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.LogSmallHeight
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Outcome

/-! # Reattach the actual small-height bound without changing the frozen payments -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

theorem highSum_small_height_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ((q.totient : ℝ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log ((q : ℝ) * v),
          source25LogKernel (sourceL N) q s) +
      (∫ y in omegaCutoff N q..v,
        heightKernel y * lambdaCountSegment N q y 0 0.36) +
      (∫ y in v..sourceT N, heightKernel y * unpaidAlpha N q y) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ)) := by
  have hsub1 : Set.uIcc (omegaCutoff N q) v ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc le_rfl hvT
  have hsub2 : Set.uIcc v (sourceT N) ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le hvT, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc huv le_rfl
  have hi := unpaidHeight_integrable hN hq
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set hsub1) (hi.mono_set hsub2)
  have h := Checked.highSum_le_unpaid_add_source32 hN hq
  rw [← he] at h
  have hs := actual_unpaid_small_height hN hq huv hvT
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hp := original_product_ge hN (q := q) le_rfl
  rw [source25_log_substitution hu huv (by linarith),
    (original_log_height_bounds hN hq).1] at hs
  linarith

theorem highSum_original_small_height_branch {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hsmall : omegaCutoff N q ≤ max (100000 / (q : ℝ)) (10000 * Real.log q)) :
    let v := min (10000 * Real.log q) (sourceT N)
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      ((q.totient : ℝ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log ((q : ℝ) * v),
          source25LogKernel (sourceL N) q s) +
      (∫ y in omegaCutoff N q..v,
        heightKernel y * lambdaCountSegment N q y 0 0.36) +
      (∫ y in v..sourceT N, heightKernel y * unpaidAlpha N q y) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ)) := by
  have hg := small_height_gate hN (q := q) le_rfl hsmall
  rw [hg.2] at hsmall
  exact highSum_small_height_split hN hq
    (le_min hsmall (WeightedLowZeros.omegaCutoff_le_sourceT hN)) (min_le_right _ _)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
