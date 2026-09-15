import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.AllPrincipal.FourPhases

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

theorem product_principal_left_values {d e : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (n : ℕ) :
    lwdProduct (lwdProduct (1 : DirichletCharacter ℂ 1) chi) psi n =
      lwdProduct chi psi n := by
  rw [lwdProduct_apply, principal_product_values, lwdProduct_apply]

theorem case_iii_g {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    lwdG (1 : DirichletCharacter ℂ 1) chi psi sigma t u v =
      zetaDamped sigma 0 + zetaDamped sigma t +
      dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK u +
      dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK v +
      dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u) +
      dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK (t + v) +
      dampedLogDeriv (lwdProduct chi psi) sigma (stechkinSigma sigma) stechkinK (u + v) +
      dampedLogDeriv (lwdProduct chi psi) sigma (stechkinSigma sigma) stechkinK (t + u + v) := by
  have h1 := general_damped_eq_of_nat_values _ _ (principal_product_values chi) hs (t + u)
  have h2 := general_damped_eq_of_nat_values _ _ (principal_product_values psi) hs (t + v)
  have h3 := general_damped_eq_of_nat_values _ _ (product_principal_left_values chi psi) hs (t + u + v)
  simp only [lwdG, h1, h2, h3, principal_damped_eq]

theorem product_eq_lifted {d e : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) :
    lwdProduct chi psi =
      chi.changeLevel (Nat.dvd_lcm_left d e) * psi.changeLevel (Nat.dvd_lcm_right d e) := by
  change chi.changeLevel _ * star ((psi⁻¹).changeLevel _) = _
  rw [map_inv, MulChar.star_eq_inv, inv_inv]

theorem principal_product_levels {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hc : chi.IsPrimitive) (hp : psi.IsPrimitive) (he : lwdProduct chi psi = 1) :
    d = e := by
  rw [product_eq_lifted] at he
  have hh := congrArg DirichletCharacter.conductor ((mul_eq_one_iff_eq_inv).mp he)
  rw [DirichletCharacter.conductor_inv, DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_changeLevel, hc, hp] at hh
  exact hh

theorem principal_product_conjugate_zeros {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hc : chi ≠ 1) (hp : psi ≠ 1) (hpc : chi.IsPrimitive) (hpp : psi.IsPrimitive)
    (he : lwdProduct chi psi = 1) {tau upsilon : ℂ}
    (ht : chi.LFunction tau = 0) (hu : psi.LFunction upsilon = 0) :
    chi.LFunction (conj upsilon) = 0 ∧ psi.LFunction (conj tau) = 0 := by
  have hde := principal_product_levels chi psi hpc hpp he
  subst e
  rw [product_eq_lifted] at he
  have hi : chi = psi⁻¹ := by
    apply DirichletCharacter.changeLevel_injective (Nat.dvd_lcm_left d d)
    rw [map_inv]
    exact (mul_eq_one_iff_eq_inv).mp he
  have hj : psi = chi⁻¹ := by rw [hi, inv_inv]
  constructor
  · rw [hi, BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj hp,
      conj_conj, hu, map_zero]
  · rw [hj, BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj hc,
      conj_conj, ht, map_zero]

theorem case_iii_constant :
    -0.8973 + 3 * 0.3316 + 4 * 0.3918 + 2 * 0.4977 +
      stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) ≤ 1.3238 := by
  have hl : 3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi ≤
      3 * 0.693147181 + 1.098612289 - 7 * 1.144729 := by
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, lwd_log_pi]
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  have hk := mul_le_mul_of_nonpos_right lwd_kappa_bounds.1
    (by norm_num : 3 * (0.693147181 : ℝ) + 1.098612289 - 7 * 1.144729 ≤ 0)
  linarith

theorem case_iii_nonprincipal_constant :
    -0.8973 + 0.3316 + 6 * 0.3918 + 2 * 0.4977 +
      stechkinConductorCoeff * (2 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) ≤ 1.3238 := by
  have hh := mul_le_mul lwd_kappa_bounds.1 Real.log_two_gt_d9.le (by norm_num)
    conductorCoeff_bounds.1
  nlinarith only [case_iii_constant, hh]

def nonprincipalCost (y : ℝ) : ℝ :=
  stechkinConductorCoeff * Real.log y - stechkinConductorCoeff * Real.log Real.pi + 0.3918

theorem case_iii_costs {x : ℝ} (hx : 0 < x) :
    -0.8973 + AllPrincipal.principalCost x + 2 * nonprincipalCost x +
      2 * nonprincipalCost (2 * x) + AllPrincipal.principalCost (2 * x) +
      AllPrincipal.principalCost (3 * x) + 2 * 0.4977 ≤
      7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  unfold nonprincipalCost AllPrincipal.principalCost
  rw [Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) hx.ne']
  nlinarith only [case_iii_constant]

theorem case_iii_nonprincipal_costs {x : ℝ} (hx : 0 < x) :
    -0.8973 + AllPrincipal.principalCost x - stechkinConductorCoeff * Real.log 2 +
      2 * nonprincipalCost x + 3 * nonprincipalCost (2 * x) +
      nonprincipalCost (3 * x) + 2 * 0.4977 ≤
      7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  unfold nonprincipalCost AllPrincipal.principalCost
  rw [Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) hx.ne']
  nlinarith only [case_iii_nonprincipal_constant]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
