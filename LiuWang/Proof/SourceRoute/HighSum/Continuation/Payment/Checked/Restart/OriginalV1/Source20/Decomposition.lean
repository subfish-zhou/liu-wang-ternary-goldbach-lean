import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Mass
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Scalar

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

def lowBase (N q : ℕ) [NeZero q] : ℝ :=
  (N : ℝ) ^ (-1 / 2 : ℝ) * sourceMass N q (1 / 2) +
    ∫ alpha in (1 / 2 : ℝ)..(19 / 20),
      layerKernel N alpha * sourceMass N q alpha

theorem sourceMass_filter {N q : ℕ} [NeZero q] {alpha : ℝ}
    (ha : 1 / 2 ≤ alpha) :
    sourceMass N q alpha =
      ∑ chi : Character q, ∑ rho ∈ (highValues N chi).filter (fun rho => alpha ≤ rho.re),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im| := by
  have hs (chi : Character q) :
      bandValues chi alpha (omegaCutoff N q) (sourceT N) =
        (highValues N chi).filter (fun rho => alpha ≤ rho.re) := by
    ext rho
    simp only [highValues, Finset.mem_filter, mem_bandValues]
    constructor
    · rintro ⟨hz, hs, hb, hu⟩
      exact ⟨⟨hz, hs, ha.trans hb, hu⟩, hb⟩
    · rintro ⟨⟨hz, hs, _, hu⟩, hb⟩
      exact ⟨hz, hs, hb, hu⟩
  simp only [sourceMass, hs]

theorem low_integrand_finite {N q : ℕ} [NeZero q] {alpha : ℝ}
    (ha : 1 / 2 ≤ alpha) :
    layerKernel N alpha * sourceMass N q alpha =
      ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
          (Set.Iic rho.re).indicator (layerKernel N) alpha := by
  rw [sourceMass_filter ha]
  simp only [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : alpha ≤ rho.re <;> simp [Set.mem_Iic, h, mul_comm]

theorem low_indicator_integrable {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    IntervalIntegrable ((Set.Iic beta).indicator (layerKernel N))
      volume (1 / 2) (19 / 20) := by
  rw [intervalIntegrable_iff]
  exact ((continuous_layerKernel hN).intervalIntegrable (1 / 2) (19 / 20)).def'.indicator
    measurableSet_Iic

theorem low_character_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) :
    IntervalIntegrable (fun alpha => ∑ rho ∈ highValues N chi,
      ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
        (Set.Iic rho.re).indicator (layerKernel N) alpha) volume (1 / 2) (19 / 20) := by
  convert! IntervalIntegrable.sum (highValues N chi) (fun rho _ =>
    (low_indicator_integrable hN rho.re).const_mul
      ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|)) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem low_integrand_integrable {N q : ℕ} [NeZero q] (hN : 0 < N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha * sourceMass N q alpha)
      volume (1 / 2) (19 / 20) := by
  have hi : IntervalIntegrable (fun alpha =>
      ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
          (Set.Iic rho.re).indicator (layerKernel N) alpha) volume (1 / 2) (19 / 20) := by
    convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
      (fun chi _ => low_character_integrable hN chi) using 1
    ext alpha
    simp only [Finset.sum_apply]
  apply hi.congr
  intro alpha ha
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 19 / 20)] at ha
  exact (low_integrand_finite ha.1.le).symm

theorem low_indicator_integral {N q : ℕ} [NeZero q] (hN : 1 ≤ N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ highValues N chi) :
    (∫ alpha in (1 / 2 : ℝ)..(19 / 20),
      (Set.Iic rho.re).indicator (layerKernel N) alpha) =
      capWeight N rho - (N : ℝ) ^ (-1 / 2 : ℝ) := by
  have hb : 1 / 2 ≤ rho.re := (mem_highValues.mp hrho).2.1
  rw [capWeight_eq_source_power hN]
  by_cases hr : rho.re ≤ 19 / 20
  · calc
      _ = ∫ alpha in (1 / 2 : ℝ)..rho.re, layerKernel N alpha :=
        intervalIntegral.integral_indicator ⟨hb, hr⟩
      _ = _ := by
        rw [WeightedHighZeros.Continuation.integral_layerKernel hN, min_eq_left hr]
        norm_num
  · have he : (∫ alpha in (1 / 2 : ℝ)..(19 / 20),
        (Set.Iic rho.re).indicator (layerKernel N) alpha) =
        ∫ alpha in (1 / 2 : ℝ)..(19 / 20), layerKernel N alpha := by
      apply intervalIntegral.integral_congr
      intro alpha ha
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 19 / 20)] at ha
      exact Set.indicator_of_mem
        (show alpha ∈ Set.Iic rho.re from ha.2.trans (le_of_not_ge hr)) _
    rw [he, WeightedHighZeros.Continuation.integral_layerKernel hN,
      min_eq_right (le_of_not_ge hr)]
    norm_num

theorem lowBase_eq_capped {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    lowBase N q = cappedHighSum N q := by
  have hi : (∫ alpha in (1 / 2 : ℝ)..(19 / 20),
      layerKernel N alpha * sourceMass N q alpha) =
      ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
          (capWeight N rho - (N : ℝ) ^ (-1 / 2 : ℝ)) := by
    calc
      _ = ∫ alpha in (1 / 2 : ℝ)..(19 / 20),
          ∑ chi : Character q, ∑ rho ∈ highValues N chi,
            ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
              (Set.Iic rho.re).indicator (layerKernel N) alpha := by
        apply intervalIntegral.integral_congr
        intro alpha ha
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 19 / 20)] at ha
        exact low_integrand_finite ha.1
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum (fun chi _ => low_character_integrable hN chi)]
        apply Finset.sum_congr rfl
        intro chi _
        rw [intervalIntegral.integral_finsetSum
          (fun rho _ => (low_indicator_integrable hN rho.re).const_mul _)]
        apply Finset.sum_congr rfl
        intro rho hrho
        rw [intervalIntegral.integral_const_mul, low_indicator_integral hN hrho]
  unfold lowBase
  rw [hi]
  change (N : ℝ) ^ (-1 / 2 : ℝ) *
    (∑ chi : Character q, ∑ rho ∈ highValues N chi,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) + _ = _
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, cappedHighSum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem original_source18 {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    highSum N q =
      (N : ℝ) ^ (-1 / 2 : ℝ) * sourceMass N q (1 / 2) +
      (∫ alpha in (1 / 2 : ℝ)..(19 / 20), layerKernel N alpha * sourceMass N q alpha) +
      (∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha) := by
  have he : excessHighSum N q =
      ∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha :=
    excessHighSum_eq_source_integral hN
  rw [← he, highSum_eq_capped_add_excess hN,
    ← lowBase_eq_capped hN]
  rfl

theorem original_source20_majorant_identity {N : ℕ} (hN : 0 < N) :
    51 * (N : ℝ) ^ (-1 / 2 : ℝ) * sourceP N * Real.log (sourceL N) ^ 2 +
      51 * sourceP N * Real.log (sourceL N) ^ 2 *
        (∫ alpha in (1 / 2 : ℝ)..(19 / 20), layerKernel N alpha) =
      51 * sourceL N ^ 3 * Real.log (sourceL N) ^ 2 * Real.exp (-sourceL N / 20) := by
  rw [WeightedHighZeros.Continuation.integral_layerKernel hN]
  rw [show (19 / 20 : ℝ) - 1 = -1 / 20 by norm_num,
    show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num, cap_level_eq_exp hN]
  unfold sourceP
  ring

theorem actual_source20_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (N : ℝ) ^ (-1 / 2 : ℝ) * sourceMass N q (1 / 2) +
      (∫ alpha in (1 / 2 : ℝ)..(19 / 20), layerKernel N alpha * sourceMass N q alpha) ≤
      Real.exp (-90) / sourceL N ^ 4 := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hb := mul_le_mul_of_nonneg_left
    (sourceMass_le_original51 (alpha := 1 / 2) hN hq (by norm_num))
    (show 0 ≤ (N : ℝ) ^ (-1 / 2 : ℝ) by positivity)
  have hi : (∫ alpha in (1 / 2 : ℝ)..(19 / 20),
      layerKernel N alpha * sourceMass N q alpha) ≤
      ∫ alpha in (1 / 2 : ℝ)..(19 / 20),
        (51 * sourceP N * Real.log (sourceL N) ^ 2) * layerKernel N alpha := by
    apply intervalIntegral.integral_mono_on (by norm_num) (low_integrand_integrable hn)
      (((continuous_layerKernel hn).intervalIntegrable _ _).const_mul _)
    intro alpha ha
    have hk : 0 ≤ layerKernel N alpha := by
      unfold layerKernel
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (by linarith [Parameters.sourceL_ge_3100 hN])
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (sourceMass_le_original51 hN hq ha.1) hk
  rw [intervalIntegral.integral_const_mul] at hi
  have hm := original_source20_majorant_identity hn
  have hs := original_source20_scalar (Parameters.sourceL_ge_3100 hN)
  nlinarith

theorem highSum_le_paid_base_add_excess {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-90) / sourceL N ^ 4 + excessHighSum N q := by
  rw [highSum_eq_capped_add_excess (Parameters.nat_pos_of_exp_le hN),
    ← lowBase_eq_capped (Parameters.nat_pos_of_exp_le hN)]
  exact add_le_add (actual_source20_paid hN hq) le_rfl

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
