import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate.Certificate
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Assembly

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

theorem actual_large_height_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N)
    (hvD : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ v) :
    (∫ y in v..sourceT N, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      (31 / 100000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have h := source26_actual_large_height hN hq hT7 huv hvT hvD
  have hp := mul_le_mul_of_nonneg_left
    (original_source26_scalar (Parameters.sourceL_ge_3100 hN))
    (show 0 ≤ (q : ℝ) / sourceL N ^ (4 : ℕ) by positivity)
  exact h.trans (hp.trans_eq (by ring))

theorem excess_after_endpoint_table {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y) :
    excessHighSum N q ≤ (18 / 100000000000 : ℝ) / sourceL N ^ (4 : ℕ) +
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
          layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * lambdaCountSegment N q y 0 0.36) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have h := source21_source32_excess_split hN hq hT7
  simp_rw [mul_add] at h
  rw [intervalIntegral.integral_add (actual_smallAlpha_height_integrable hN hq)
    (lowLambda_height_integrable hN hq)] at h
  linarith

theorem assembly_large_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q) :
    excessHighSum N q ≤ (18 / 100000000000 : ℝ) / sourceL N ^ (4 : ℕ) +
      (31 / 100000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
      (∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * lambdaCountSegment N q y 0 0.36) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have hp := actual_large_height_paid hN hq hT7 le_rfl
    (WeightedLowZeros.omegaCutoff_le_sourceT hN) hlarge
  linarith [excess_after_endpoint_table hN hq hT7]

theorem assembly_small_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < max (100000 / (q : ℝ)) (10000 * Real.log q)) :
    excessHighSum N q ≤ (18 / 100000000000 : ℝ) / sourceL N ^ (4 : ℕ) +
      (∫ y in omegaCutoff N q..max (100000 / (q : ℝ)) (10000 * Real.log q),
        heightKernel y *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (31 / 100000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
      (∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * lambdaCountSegment N q y 0 0.36) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  let v := max (100000 / (q : ℝ)) (10000 * Real.log q)
  have huv : omegaCutoff N q ≤ v := hsmall.le
  have hvT : v ≤ sourceT N := source21_height_domain hN hq
  have hs1 : Set.uIcc (omegaCutoff N q) v ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc le_rfl hvT
  have hs2 : Set.uIcc v (sourceT N) ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le hvT, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc huv le_rfl
  have hi := actual_smallAlpha_height_integrable hN hq
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set hs1) (hi.mono_set hs2)
  have h := excess_after_endpoint_table hN hq hT7
  rw [← he] at h
  have hp := actual_large_height_paid hN hq hT7 huv hvT le_rfl
  linarith

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
