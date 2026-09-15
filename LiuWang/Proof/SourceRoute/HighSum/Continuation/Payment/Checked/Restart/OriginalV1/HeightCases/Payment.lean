import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases.Comparison

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases

theorem actual_slice_common {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N))
    (hT1 : strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4) :
    lambdaCountSegment N q y (1 / c1) 0.36 ≤
      profile35 (sourceL N) (Real.log ((q : ℝ) * y)) := by
  rcases actual_height_classification q y with h1 | ⟨_, h2⟩ | h3
  · exact actual_source35_slice hN hq hy.1 h1
  · exact (actual_source36_slice hN hq hy.1 h2).trans
      (profile36_le_profile35 (actual_ratio_ge_twenty hN hq hy))
  · have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
    have hs : 0 < Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy.1]
    exact (actual_third_slice hN hq hy.1 h3 hT1).trans
      (third_le_profile35 hL hs (actual_ratio_ge_twenty hN hq hy))

theorem finiteK3_le_common_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4) :
    finiteK3 N q ≤ heightEnvelope profile35 N q := by
  apply intervalIntegral.integral_mono_on (WeightedLowZeros.omegaCutoff_le_sourceT hN)
    (band_height_integrable hN hq c1_bounds.1.le (by linarith [c1_bounds.2.1]) (by norm_num))
    (envelope_integrable profile35_continuousOn hN hq)
  intro y hy
  exact mul_le_mul_of_nonneg_left (actual_slice_common hN hq hy (hT1 y hy))
    (by unfold heightKernel; positivity)

theorem finiteK3_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4) :
    finiteK3 N q ≤ 0.0102654 * q / sourceL N ^ 4 :=
  (finiteK3_le_common_height hN hq hT1).trans (source35_height_paid hN hq)

theorem actual_lambda_with_zero_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT1 : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      strictFamilyCount q (1 - 0.26213 / Real.log ((q : ℝ) * y)) y ≤ 4) :
    (∫ y in omegaCutoff N q..sourceT N, heightKernel y * lambdaCountSegment N q y 0 0.36) ≤
      zeroTail N q + 0.0102654 * q / sourceL N ^ 4 := by
  rw [original_height_zero_tail hN hq]
  exact add_le_add le_rfl (finiteK3_paid hN hq hT1)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases
