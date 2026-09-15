import LiuWang.Proof.WeightedHighZeros.Continuation.Frontier.Scalar

/-! # Paying the old cap and the entire intermediate source integral together -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

def frontierCap (N q : ℕ) [NeZero q] : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ highValues N chi,
    (analyticOrderNatAt chi.LFunction rho : ℝ) *
      (min ((N : ℝ) ^ (rho.re - 1)) ((N : ℝ) ^ (-1 / 50 : ℝ)) / |rho.im|)

theorem frontierCap_le_reciprocal (N q : ℕ) [NeZero q] :
    frontierCap N q ≤ (N : ℝ) ^ (-1 / 50 : ℝ) *
      bandSum 1 q (omegaCutoff N q) (sourceT N) := by
  calc
    _ ≤ ∑ chi : Character q, ∑ rho ∈ highValues N chi,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((N : ℝ) ^ (-1 / 50 : ℝ) / |rho.im|) := by
      exact Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ =>
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (min_le_right _ _) (abs_nonneg _)) (Nat.cast_nonneg _)))
    _ = _ := by
      simp only [bandSum, highValues, Nat.cast_one, Real.one_rpow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      apply Finset.sum_congr rfl
      intro rho _
      ring

theorem frontierCap_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    frontierCap N q ≤ (1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hs := (frontierCap_le_reciprocal N q).trans
    (mul_le_mul_of_nonneg_left (actual_reciprocal_le hN hq) (by positivity))
  have he : (N : ℝ) ^ (-1 / 50 : ℝ) = Real.exp (-sourceL N / 50) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
    congr 1
    unfold sourceL
    ring
  rw [he] at hs
  have hp := mul_le_mul_of_nonneg_right
    (frontier_scalar_payment (Parameters.sourceL_ge_3100 hN)) (Nat.cast_nonneg q)
  exact hs.trans (by convert hp using 1 <;> ring)

theorem middle_indicator_integrable {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    IntervalIntegrable ((Set.Iic beta).indicator (layerKernel N))
      volume (19 / 20) (49 / 50) := by
  rw [intervalIntegrable_iff]
  exact ((continuous_layerKernel hN).intervalIntegrable (19 / 20) (49 / 50)).def'.indicator
    measurableSet_Iic

theorem middle_indicator_integral {N : ℕ} (hN : 0 < N) {beta : ℝ}
    (hb : 19 / 20 ≤ beta) :
    (∫ alpha in (19 / 20 : ℝ)..(49 / 50),
      (Set.Iic beta).indicator (layerKernel N) alpha) =
      (N : ℝ) ^ (min beta (49 / 50) - 1) - (N : ℝ) ^ (-1 / 20 : ℝ) := by
  by_cases h : beta ≤ 49 / 50
  · rw [min_eq_left h]
    calc
      _ = ∫ alpha in (19 / 20 : ℝ)..beta, layerKernel N alpha :=
        intervalIntegral.integral_indicator ⟨hb, h⟩
      _ = _ := by rw [integral_layerKernel hN]; norm_num
  · rw [min_eq_right (le_of_not_ge h)]
    calc
      _ = ∫ alpha in (19 / 20 : ℝ)..(49 / 50), layerKernel N alpha := by
        apply intervalIntegral.integral_congr
        intro alpha ha
        rw [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 49 / 50)] at ha
        exact Set.indicator_of_mem (show alpha ∈ Set.Iic beta by
          exact ha.2.trans (le_of_not_ge h)) _
      _ = _ := by rw [integral_layerKernel hN]; norm_num

theorem middle_character_integrable {N q : ℕ} [NeZero q] (hN : 0 < N)
    (chi : Character q) :
    IntervalIntegrable (fun alpha => ∑ rho ∈ rightValues N chi,
      ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
        (Set.Iic rho.re).indicator (layerKernel N) alpha) volume (19 / 20) (49 / 50) := by
  convert! IntervalIntegrable.sum (rightValues N chi) (fun rho _ =>
      (middle_indicator_integrable hN rho.re).const_mul
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|)) using 1
  ext alpha
  simp only [Finset.sum_apply]

theorem middle_source_eq_finite {N q : ℕ} [NeZero q] (hN : 0 < N) :
    (∫ alpha in (19 / 20 : ℝ)..(49 / 50),
      layerKernel N alpha * sourceMass N q alpha) =
      ∑ chi : Character q, ∑ rho ∈ rightValues N chi,
        ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) *
          ((N : ℝ) ^ (min rho.re (49 / 50) - 1) - (N : ℝ) ^ (-1 / 20 : ℝ)) := by
  have he : (∫ alpha in (19 / 20 : ℝ)..(49 / 50),
      layerKernel N alpha * sourceMass N q alpha) =
      ∫ alpha in (19 / 20 : ℝ)..(49 / 50),
        layerKernel N alpha * rightMass N q alpha := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro alpha ha
    change layerKernel N alpha * sourceMass N q alpha =
      layerKernel N alpha * rightMass N q alpha
    rw [rightMass_eq_source_band ha.1]
    rfl
  rw [he]
  simp_rw [layer_integrand_eq_finite]
  rw [intervalIntegral.integral_finsetSum (fun chi _ => middle_character_integrable hN chi)]
  apply Finset.sum_congr rfl
  intro chi _
  rw [intervalIntegral.integral_finsetSum (fun rho _ =>
    (middle_indicator_integrable hN rho.re).const_mul _)]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [intervalIntegral.integral_const_mul,
    middle_indicator_integral hN (Finset.mem_filter.mp hrho).2.le]

theorem frontierCap_eq_old_cap_add_middle {N q : ℕ} [NeZero q] (hN : 1 ≤ N) :
    frontierCap N q = cappedHighSum N q +
      ∫ alpha in (19 / 20 : ℝ)..(49 / 50),
        layerKernel N alpha * sourceMass N q alpha := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [middle_source_eq_finite hN]
  symm
  unfold cappedHighSum frontierCap rightValues
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro chi _
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hr : 19 / 20 < rho.re
  · have h19 : (N : ℝ) ^ (-1 / 20 : ℝ) ≤ (N : ℝ) ^ (rho.re - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [if_pos hr, capWeight, min_eq_right h19]
    by_cases h49 : rho.re ≤ 49 / 50
    · have hh : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 50 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      rw [min_eq_left h49, min_eq_left hh]
      ring
    · have hh : (N : ℝ) ^ (-1 / 50 : ℝ) ≤ (N : ℝ) ^ (rho.re - 1) :=
        Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      rw [min_eq_right (le_of_not_ge h49), min_eq_right hh]
      norm_num
      ring
  · have h19 : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    have h49 : (N : ℝ) ^ (rho.re - 1) ≤ (N : ℝ) ^ (-1 / 50 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    rw [if_neg hr, capWeight, min_eq_left h19, min_eq_left h49, add_zero]

theorem old_cap_and_middle_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    cappedHighSum N q + (∫ alpha in (19 / 20 : ℝ)..(49 / 50),
      layerKernel N alpha * sourceMass N q alpha) ≤
        (1 / 10000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  rw [← frontierCap_eq_old_cap_add_middle (Parameters.nat_pos_of_exp_le hN)]
  exact frontierCap_paid hN hq

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
