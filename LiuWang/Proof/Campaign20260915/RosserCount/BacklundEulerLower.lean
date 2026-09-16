import LiuWang.Proof.Campaign20260915.RosserCount.BacklundCenterReuse
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

set_option autoImplicit false
noncomputable section

open Complex Filter Finset
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_euler_factor_lower {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : 1 < p) :
    ‖(1 - (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)))⁻¹‖ ≤
      ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ * ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  let u : ℝ := (p : ℝ) ^ (-s.re)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by positivity) _
  have hu1 : u < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  have hu : ‖(p : ℂ) ^ (-s)‖ = u := by
    rw [norm_natCast_cpow_of_pos (by omega)]
    rfl
  have huC : (p : ℂ) ^ (-(s.re : ℂ)) = (u : ℂ) := by
    dsimp [u]
    rw [← ofReal_neg, ← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg p)]
  have h2C : (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)) = ((u ^ 2 : ℝ) : ℂ) := by
    rw [show -((2 * s.re : ℝ) : ℂ) = -(s.re : ℂ) * (2 : ℕ) by push_cast; ring,
      cpow_mul_nat, huC, ofReal_pow]
  have hn : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + u := by
    simpa only [norm_one, hu] using norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
  have hz : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hu
    linarith
  have h1 : ‖1 - (p : ℂ) ^ (-(s.re : ℂ))‖ = 1 - u := by
    rw [huC, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have h2 : ‖1 - (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ))‖ = 1 - u ^ 2 := by
    rw [h2C, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith)]
  simp only [norm_inv, h1, h2]
  rw [← mul_inv_rev]
  simp only [← one_div]
  apply one_div_le_one_div_of_le (by positivity : 0 <
    (1 - u) * ‖1 - (p : ℂ) ^ (-s)‖)
  nlinarith [mul_le_mul_of_nonneg_right hn (show 0 ≤ 1 - u by linarith)]

theorem backlund_zeta_euler_lower {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤
      ‖riemannZeta s‖ * ‖riemannZeta (s.re : ℂ)‖ := by
  have h1 : 1 < (s.re : ℂ).re := by simpa using hs
  have h2 : 1 < ((2 * s.re : ℝ) : ℂ).re := by simp only [ofReal_re]; linarith
  apply le_of_tendsto_of_tendsto (riemannZeta_eulerProduct h2).norm
    ((riemannZeta_eulerProduct hs).norm.mul (riemannZeta_eulerProduct h1).norm)
  filter_upwards [] with n
  simp only [norm_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  exact backlund_euler_factor_lower hs (Nat.mem_primesBelow.mp hp).2.one_lt

theorem backlund_center_log_lower :
    ∀ T : ℝ, Real.log ‖riemannZeta (5 / 2 : ℂ)‖ -
      Real.log ‖riemannZeta (5 / 4 : ℂ)‖ ≤
        Real.log ‖riemannZeta (backlundCenterPoint T)‖ := by
  intro T
  have h := backlund_zeta_euler_lower (s := backlundCenterPoint T)
    (by norm_num [backlundCenterPoint])
  norm_num [backlundCenterPoint] at h
  change ‖riemannZeta (5 / 2 : ℂ)‖ ≤
    ‖riemannZeta (backlundCenterPoint T)‖ * ‖riemannZeta (5 / 4 : ℂ)‖ at h
  have hz : 0 < ‖riemannZeta (5 / 2 : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hc : 0 < ‖riemannZeta (5 / 4 : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hl := Real.log_le_log hz h
  rw [Real.log_mul (norm_pos_iff.mpr (backlundCenter_nonzero T)).ne' hc.ne'] at hl
  linarith

#print axioms backlund_euler_factor_lower
#print axioms backlund_zeta_euler_lower
#print axioms backlund_center_log_lower

end LiuWang.Proof.Campaign20260915.RosserCount
