import LiuWang.Proof.Campaign20260915.HighSums.CompensatedExcess
import LiuWang.Proof.Campaign20260915.HighSums.ZeroTailSupport

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.WeightedHighZeros.Continuation
open LiuWang.Proof.SourceRoute.HighSum
open LiuWang.Proof.SourceRoute.HighSum.Continuation
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.Campaign20260915.HighSums

theorem count_le_below_height_of_real {q : ℕ} [NeZero q] (chi : Character q)
    {alpha y u : ℝ} (hu : 0 < u)
    (hreal : ∀ rho ∈ zeroValues chi alpha y, rho.im = 0) :
    count chi alpha y ≤ belowHeightCount chi alpha u := by
  apply Finset.sum_le_sum_of_subset
  intro rho hrho
  obtain ⟨hz, ⟨h0, h1, _⟩, ha⟩ := mem_zeroValues.mp hrho
  have ht : |rho.im| < u := by simpa only [hreal rho hrho, abs_zero] using hu
  exact Finset.mem_filter.mpr ⟨mem_zeroValues.mpr ⟨hz, ⟨h0, h1, ht.le⟩, ha⟩, ht⟩

theorem below_height_layer_mass_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha *
      (belowHeightFamilyCount q alpha (omegaCutoff N q) : ℝ))
      volume (19 / 20) 1 := by
  have hu : omegaCutoff N q ≠ 0 := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  convert (below_height_layer_integrable hN hq).mul_const (omegaCutoff N q) using 1
  ext alpha
  field_simp

theorem below_height_layer_mass {N q : ℕ} [NeZero q]
    (_hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha *
      (belowHeightFamilyCount q alpha (omegaCutoff N q) : ℝ)) =
        omegaCutoff N q * belowHeightLayerCorrection N q := by
  have hu : omegaCutoff N q ≠ 0 := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  unfold belowHeightLayerCorrection
  simp_rw [← mul_div_assoc, intervalIntegral.integral_div]
  field_simp

theorem tail_slice_le_below_height_mass {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y)
    (hreal : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ zeroValues chi 0 y →
      1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0) :
    lambdaCountSegment N q y 0 (1 / c1) ≤
      omegaCutoff N q * belowHeightLayerCorrection N q := by
  let a : ℝ := 1 - (1 / c1) / Real.log ((q : ℝ) * y)
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have ha : 19 / 20 ≤ a := by
    have hc : (1 / c1 : ℝ) ≤ 0.478 := by linarith [c1_bounds.2.1]
    exact (original_alpha_cutoff_mem hN hy).1.trans
      (sub_le_sub_left (div_le_div_of_nonneg_right hc hs.le) 1)
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    linarith [div_nonneg c1_bounds.1.le hs.le]
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hk (alpha : ℝ) : 0 ≤ layerKernel N alpha :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL
  have hsub : Set.uIcc a 1 ⊆ Set.uIcc (19 / 20 : ℝ) 1 := by
    rw [Set.uIcc_of_le ha1, Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc ha le_rfl
  have he : lambdaCountSegment N q y 0 (1 / c1) =
      ∫ alpha in a..1, layerKernel N alpha * (familyCount q alpha y : ℝ) := by
    symm
    simpa only [lambdaCountSegment, lambdaCountIntegrand, a, zero_div, sub_zero] using
      actual_lambda_substitution N q y (Real.log ((q : ℝ) * y)) 0 (1 / c1)
  rw [he, ← below_height_layer_mass hN hq]
  calc
    _ ≤ ∫ alpha in a..1, layerKernel N alpha *
        (belowHeightFamilyCount q alpha (omegaCutoff N q) : ℝ) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ha1
        ((family_alpha_integrable (q := q) (Parameters.nat_pos_of_exp_le hN) y).mono_set hsub)
        ((below_height_layer_mass_integrable hN hq).mono_set hsub)
      intro alpha halpha
      apply mul_le_mul_of_nonneg_left _ (hk alpha)
      apply Nat.cast_le.mpr
      apply Finset.sum_le_sum
      intro chi _
      apply count_le_below_height_of_real chi hu
      intro rho hrho
      obtain ⟨hz, ⟨h0, h1, ht⟩, hb⟩ := mem_zeroValues.mp hrho
      exact hreal chi rho (mem_zeroValues.mpr ⟨hz, ⟨h0, h1, ht⟩, h0.le⟩)
        (halpha.1.trans_le hb)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval ha ha1 le_rfl
        _ (below_height_layer_mass_integrable hN hq)
      exact ae_of_all _ (fun alpha => mul_nonneg (hk alpha) (Nat.cast_nonneg _))

/-- The strict near-one real-zero classification is the still-unpaid M05 input. -/
theorem zeroTail_le_compensation_of_near_one_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hreal : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ), rho ∈ zeroValues chi 0 y →
        1 - (1 / c1) / Real.log ((q : ℝ) * y) < rho.re → rho.im = 0) :
    zeroTail N q ≤ belowHeightLayerCorrection N q := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have hT : 0 < sourceT N := hu.trans_le huT
  have hC := belowHeightLayerCorrection_nonneg hN hq
  have hh : zeroTail N q ≤
      ∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * (omegaCutoff N q * belowHeightLayerCorrection N q) := by
    apply intervalIntegral.integral_mono_on huT
      (band_height_integrable hN hq le_rfl c1_bounds.1.le
        (by linarith [c1_bounds.2.1]))
      ((heightKernel_integrable hu huT).mul_const _)
    intro y hy
    exact mul_le_mul_of_nonneg_left
      (tail_slice_le_below_height_mass hN hq hy.1 (hreal y hy))
      (by unfold heightKernel; positivity)
  rw [intervalIntegral.integral_mul_const, integral_heightKernel hu huT] at hh
  have he :
      (1 / omegaCutoff N q - 1 / sourceT N) *
        (omegaCutoff N q * belowHeightLayerCorrection N q) =
      belowHeightLayerCorrection N q -
        omegaCutoff N q / sourceT N * belowHeightLayerCorrection N q := by
    field_simp
  rw [he] at hh
  exact hh.trans (sub_le_self _ (mul_nonneg (div_nonneg hu.le hT.le) hC))

#print axioms count_le_below_height_of_real
#print axioms zeroTail_le_compensation_of_near_one_real

end LiuWang.Proof.Campaign20260915.HighSums
