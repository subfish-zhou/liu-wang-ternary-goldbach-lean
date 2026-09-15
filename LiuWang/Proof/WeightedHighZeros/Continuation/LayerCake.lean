import LiuWang.Proof.WeightedHighZeros.Continuation.Capped
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact finite layer-cake identity for the unpaid high-alpha excess

Every coefficient is the ordinary-L analytic multiplicity on the same closed
height band. The integrability and finite interchange are proved, not assumed.
This is a consumer identity, not a new zero-density producer.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation

def rightValues {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : Finset ℂ :=
  (highValues N chi).filter (fun rho => 19 / 20 < rho.re)

def rightMass (N q : ℕ) [NeZero q] (alpha : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ (rightValues N chi).filter (fun rho => alpha ≤ rho.re),
    (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|

def layerKernel (N : ℕ) (alpha : ℝ) : ℝ :=
  (N : ℝ) ^ (alpha - 1) * sourceL N

theorem continuous_layerKernel {N : ℕ} (hN : 0 < N) :
    Continuous (layerKernel N) := by
  unfold layerKernel
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn0 : (N : ℝ) ≠ 0 := hn.ne'
  fun_prop

theorem integral_layerKernel {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    (∫ alpha in a..b, layerKernel N alpha) =
      (N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro alpha _
    have h := ((hasDerivAt_id alpha).sub_const 1).const_rpow (Nat.cast_pos.mpr hN)
    simpa only [layerKernel, sourceL, id_eq, mul_one, mul_comm, one_mul] using h
  · exact (continuous_layerKernel hN).intervalIntegrable _ _

theorem indicator_layer_integrable {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    IntervalIntegrable ((Set.Iic beta).indicator (layerKernel N)) volume (19 / 20) 1 := by
  rw [intervalIntegrable_iff]
  exact ((continuous_layerKernel hN).intervalIntegrable (19 / 20) 1).def'.indicator
    measurableSet_Iic

theorem right_indicator_integral {N q : ℕ} [NeZero q] (hN : 0 < N)
    {chi : Character q} {rho : ℂ} (hrho : rho ∈ rightValues N chi) :
    (∫ alpha in (19 / 20 : ℝ)..1, (Set.Iic rho.re).indicator (layerKernel N) alpha) =
      (N : ℝ) ^ (rho.re - 1) - (N : ℝ) ^ (-1 / 20 : ℝ) := by
  have hv := Finset.mem_filter.mp hrho
  have hb := (mem_highValues.mp hv.1).2.2.1
  calc
    _ = ∫ alpha in (19 / 20 : ℝ)..rho.re, layerKernel N alpha :=
      intervalIntegral.integral_indicator ⟨hv.2.le, hb.le⟩
    _ = _ := by rw [integral_layerKernel hN]; norm_num

theorem layer_integrand_eq_finite (N q : ℕ) [NeZero q] (alpha : ℝ) :
    layerKernel N alpha * rightMass N q alpha =
      ∑ chi : Character q, ∑ rho ∈ rightValues N chi,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
          (Set.Iic rho.re).indicator (layerKernel N) alpha := by
  simp only [rightMass, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  by_cases ha : alpha ≤ rho.re
  · simp [Set.indicator_of_mem, Set.mem_Iic, ha, mul_comm]
  · simp [Set.indicator_of_notMem, Set.mem_Iic, ha]

theorem right_character_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) :
    IntervalIntegrable (fun alpha => ∑ rho ∈ rightValues N chi,
      ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
        (Set.Iic rho.re).indicator (layerKernel N) alpha) volume (19 / 20) 1 := by
  convert! IntervalIntegrable.sum (rightValues N chi) (fun rho _ =>
      (indicator_layer_integrable hN rho.re).const_mul
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|)) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem layer_integrand_integrable {N q : ℕ} [NeZero q] (hN : 0 < N) :
    IntervalIntegrable (fun alpha => layerKernel N alpha * rightMass N q alpha)
      volume (19 / 20) 1 := by
  simp_rw [layer_integrand_eq_finite]
  convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
      (fun chi _ => right_character_integrable hN chi) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem excessHighSum_eq_integral {N q : ℕ} [NeZero q] (hN : 0 < N) :
    excessHighSum N q =
      ∫ alpha in (19 / 20 : ℝ)..1,
        (N : ℝ) ^ (alpha - 1) * sourceL N * rightMass N q alpha := by
  change _ = ∫ alpha in (19 / 20 : ℝ)..1, layerKernel N alpha * rightMass N q alpha
  simp_rw [layer_integrand_eq_finite]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro chi _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro rho hrho
      rw [intervalIntegral.integral_const_mul, right_indicator_integral hN hrho]
      ring
    · intro rho _
      exact (indicator_layer_integrable hN rho.re).const_mul _
  · intro chi _
    exact right_character_integrable hN chi

theorem rightMass_eq_source_band {N q : ℕ} [NeZero q] {alpha : ℝ}
    (ha : 19 / 20 < alpha) :
    rightMass N q alpha =
      ∑ chi : Character q, ∑ rho ∈ bandValues chi alpha (omegaCutoff N q) (sourceT N),
        (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im| := by
  have hsets (chi : Character q) :
      (rightValues N chi).filter (fun rho => alpha ≤ rho.re) =
        bandValues chi alpha (omegaCutoff N q) (sourceT N) := by
    ext rho
    simp only [rightValues, Finset.mem_filter, highValues, mem_bandValues]
    constructor
    · rintro ⟨⟨⟨hz, hs, _, hu⟩, _⟩, hb⟩
      exact ⟨hz, hs, hb, hu⟩
    · rintro ⟨hz, hs, hb, hu⟩
      exact ⟨⟨⟨hz, hs, by linarith, hu⟩, by linarith⟩, hb⟩
  simp only [rightMass, hsets]

theorem original_threshold_integral_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ∫ alpha in (19 / 20 : ℝ)..1,
        (N : ℝ) ^ (alpha - 1) * sourceL N * rightMass N q alpha := by
  rw [← excessHighSum_eq_integral (Parameters.nat_pos_of_exp_le hN)]
  exact original_threshold_reduction hN hq

end LiuWang.Proof.WeightedHighZeros.Continuation
