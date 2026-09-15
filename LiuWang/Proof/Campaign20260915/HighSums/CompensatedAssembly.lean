import LiuWang.Proof.Campaign20260915.HighSums.CompensatedExcess
import LiuWang.Proof.Campaign20260915.HighSums.ZeroTailSupport
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.Assembly
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source27.Difference

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation
open LiuWang.Proof.SourceRoute.HighSum LiuWang.Proof.SourceRoute.HighSum.Continuation
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.Campaign20260915.HighSums

theorem source36_full_lambda_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0 0.36) ≤
        0.0016 * q / sourceL N ^ 4 := by
  rw [original_height_zero_tail hN hq, zeroTail_zero_of_second hN hq hcase, zero_add]
  exact actual_source36 hN hq hcase

theorem highSum_large_height_second_without_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      0.0016 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  have hh := Source20.highSum_large_height hN hq hT7 hlarge
  have hp := source36_full_lambda_paid hN hq hcase
  linarith

theorem compensated_excess_after_endpoint_table {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y) :
    excessHighSum N q + belowHeightLayerCorrection N q ≤
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
          layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      (∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * lambdaCountSegment N q y 0 0.36) +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 := by
  have he := excessHighSum_add_belowHeightLayerCorrection hN hq
  rw [original_height_eq_unpaid_add_table hN hq] at he
  have hs :
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y * unpaidAlpha N q y) =
        (∫ y in omegaCutoff N q..sourceT N, heightKernel y *
          ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
            layerKernel N alpha * (familyCount q alpha y : ℝ)) +
        ∫ y in omegaCutoff N q..sourceT N,
          heightKernel y * lambdaCountSegment N q y 0 0.36 := by
    rw [← intervalIntegral.integral_add (actual_smallAlpha_height_integrable hN hq)
      (lowLambda_height_integrable hN hq)]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)] at hy
    dsimp only
    rw [unpaidAlpha_eq_original_ranges hN hy.1, mul_add]
  rw [hs] at he
  linarith [source21_endpoint_integral hN hq hT7, Checked.actual_source32 hN hq]

theorem compensated_highSum_large_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hlarge : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ omegaCutoff N q) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 -
      belowHeightLayerCorrection N q := by
  have he := compensated_excess_after_endpoint_table hN hq hT7
  rw [original_height_zero_tail hN hq] at he
  have hp := Source26Certificate.actual_large_height_paid hN hq hT7 le_rfl
    (WeightedLowZeros.omegaCutoff_le_sourceT hN) hlarge
  have hk := HeightCases.finiteK3_paid hN hq hT1
  have hb := Source20.highSum_le_paid_base_add_excess hN hq
  linarith

theorem compensated_highSum_small_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hsmall : omegaCutoff N q < Source27.q1 q) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 +
      (18 / 100000000000 : ℝ) / sourceL N ^ 4 +
      (197 / 100000 : ℝ) * q / sourceL N ^ 4 +
      (q : ℝ) / sourceL N ^ 4 *
        Source27.transferRemainder (sourceL N) q q.totient
          (Real.log ((q : ℝ) * Source27.q1 q)) +
      (31 / 100000 : ℝ) * q / sourceL N ^ 4 +
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 +
      (368 / 1000000000000000 : ℝ) * q / sourceL N ^ 4 -
      belowHeightLayerCorrection N q := by
  have huv := hsmall.le
  have hvT : Source27.q1 q ≤ sourceT N := source21_height_domain hN hq
  have hs1 : Set.uIcc (omegaCutoff N q) (Source27.q1 q) ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc le_rfl hvT
  have hs2 : Set.uIcc (Source27.q1 q) (sourceT N) ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le hvT, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc huv le_rfl
  have hi := actual_smallAlpha_height_integrable hN hq
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set hs1) (hi.mono_set hs2)
  have he := compensated_excess_after_endpoint_table hN hq hT7
  rw [← hsplit, original_height_zero_tail hN hq] at he
  have hp := Source26Certificate.actual_large_height_paid hN hq hT7 huv hvT le_rfl
  have hshort := Source27.actualShort_le_literal_add_remainder hN hq hsmall
  have hs := mul_le_mul_of_nonneg_left
    (Source27.scalar_uniform (Parameters.sourceL_ge_3100 hN))
    (show 0 ≤ (q : ℝ) / sourceL N ^ 4 by positivity)
  have hs' :
      (q : ℝ) / sourceL N ^ 4 * Source27.scalar (sourceL N) ≤
      (197 / 100000 : ℝ) * q / sourceL N ^ 4 :=
    hs.trans_eq (by ring)
  unfold Source27.actualShort at hshort
  rw [mul_add] at hshort
  have hk := HeightCases.finiteK3_paid hN hq hT1
  have hb := Source20.highSum_le_paid_base_add_excess hN hq
  linarith only [he, hp, hshort, hs', hk, hb]

#print axioms compensated_highSum_large_height
#print axioms compensated_highSum_small_height
#print axioms source36_full_lambda_paid
#print axioms highSum_large_height_second_without_tail

end LiuWang.Proof.Campaign20260915.HighSums
