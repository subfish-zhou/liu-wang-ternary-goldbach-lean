import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.Abel
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section

open Finset Set
open scoped ArithmeticFunction.Moebius

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

theorem euler_density_bounds :
    (0.6 : ℝ) ≤ 6 / Real.pi ^ 2 ∧ 6 / Real.pi ^ 2 ≤ 0.608 := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Real.pi_gt_d4, Real.pi_pos]

private theorem inv_sqrt_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (Real.sqrt t)⁻¹)
      (-(1 / (2 * x * Real.sqrt x))) x := by
  convert! (Real.hasDerivAt_sqrt hx.ne').inv (Real.sqrt_pos.mpr hx).ne' using 1
  rw [Real.sq_sqrt hx.le]
  field_simp

private theorem sqrt_primitive_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ =>
      6 / Real.pi ^ 2 * Real.sqrt t + Real.log t - (Real.sqrt t)⁻¹)
      (1 / (2 * x * Real.sqrt x) * countMajorant x) x := by
  convert! (((Real.hasDerivAt_sqrt hx.ne').const_mul (6 / Real.pi ^ 2)).add
    (Real.hasDerivAt_log hx.ne')).sub (inv_sqrt_deriv hx) using 1
  unfold countMajorant
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

private theorem harmonic_primitive_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ =>
      6 / Real.pi ^ 2 * Real.log t - 4 * (Real.sqrt t)⁻¹ - t⁻¹)
      ((x ^ 2)⁻¹ * countMajorant x) x := by
  convert! (((Real.hasDerivAt_log hx.ne').const_mul (6 / Real.pi ^ 2)).sub
    ((inv_sqrt_deriv hx).const_mul 4)).sub (hasDerivAt_inv hx.ne') using 1
  unfold countMajorant
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

theorem weighted_sqrt_abel {y : ℝ} (hy : 1 ≤ y) :
    weightedSum y (fun t => (Real.sqrt t)⁻¹) ≤
      2 * (6 / Real.pi ^ 2) * Real.sqrt y + Real.log y + 3 - 6 / Real.pi ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have h := abel_upper hy (fun t => (Real.sqrt t)⁻¹)
    (fun t => -(1 / (2 * t * Real.sqrt t)))
    (fun t => 6 / Real.pi ^ 2 * Real.sqrt t + Real.log t - (Real.sqrt t)⁻¹)
    (fun x hx => inv_sqrt_deriv (by linarith [hx.1]))
    (by
      apply ContinuousOn.neg
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        exact (mul_pos (mul_pos (by norm_num) hx0) (Real.sqrt_pos.mpr hx0)).ne')
    (inv_nonneg.mpr hs0.le)
    (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      exact neg_nonpos.mpr (by positivity))
    (fun x hx => by simpa only [neg_neg] using sqrt_primitive_deriv (by linarith [hx.1]))
  apply h.trans_eq
  simp only [countMajorant, Real.sqrt_one, Real.log_one, inv_one, mul_one, add_zero]
  field_simp
  nlinarith [Real.sq_sqrt hy0.le]

theorem weighted_harmonic_abel {y : ℝ} (hy : 1 ≤ y) :
    weightedSum y (fun t => t⁻¹) ≤
      (6 / Real.pi ^ 2) * Real.log y + 6 / Real.pi ^ 2 + 5 -
        2 * (Real.sqrt y)⁻¹ := by
  have hy0 : 0 < y := by linarith
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have h := abel_upper hy (fun t => t⁻¹) (fun t => -(t ^ 2)⁻¹)
    (fun t => 6 / Real.pi ^ 2 * Real.log t - 4 * (Real.sqrt t)⁻¹ - t⁻¹)
    (fun x hx => hasDerivAt_inv (by linarith [hx.1]))
    (by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (by fun_prop)
      intro x hx
      exact pow_ne_zero 2 (by linarith [hx.1]))
    (inv_nonneg.mpr hy0.le)
    (fun x _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x)))
    (fun x hx => by simpa only [neg_neg] using harmonic_primitive_deriv (by linarith [hx.1]))
  apply h.trans_eq
  simp only [countMajorant, Real.sqrt_one, Real.log_one, inv_one, mul_zero]
  field_simp
  nlinarith [Real.sq_sqrt hy0.le]

theorem equation_11 {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ positiveBelow y, |(μ n : ℝ)| / Real.sqrt n) ≤
      1.216 * Real.sqrt y + Real.log y + 2.4 := by
  have h := weighted_sqrt_abel hy
  have he : weightedSum y (fun t => (Real.sqrt t)⁻¹) =
      ∑ n ∈ positiveBelow y, |(μ n : ℝ)| / Real.sqrt n := by
    simp [weightedSum, div_eq_mul_inv, mul_comm]
  rw [he] at h
  have hC := euler_density_bounds
  have hm := mul_le_mul_of_nonneg_right hC.2 (Real.sqrt_nonneg y)
  linarith

theorem equation_12 {y : ℝ} (hy : 1 ≤ y) :
    (∑ n ∈ positiveBelow y, |(μ n : ℝ)| / (n : ℝ)) ≤
      0.608 * Real.log y + 5.608 := by
  have h := weighted_harmonic_abel hy
  have he : weightedSum y (fun t => t⁻¹) =
      ∑ n ∈ positiveBelow y, |(μ n : ℝ)| / (n : ℝ) := by
    simp [weightedSum, div_eq_mul_inv, mul_comm]
  rw [he] at h
  have hC := euler_density_bounds
  have hm := mul_le_mul_of_nonneg_right hC.2 (Real.log_nonneg hy)
  have hi := inv_nonneg.mpr (Real.sqrt_nonneg y)
  linarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic
