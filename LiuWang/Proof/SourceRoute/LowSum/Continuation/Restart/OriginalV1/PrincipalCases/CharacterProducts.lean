import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases.Kernels

set_option autoImplicit false
noncomputable section

open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

theorem modOne_principal_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
  apply MulChar.one_apply
  rw [Subsingleton.elim (n : ZMod 1) 1]
  exact isUnit_one

theorem principal_product_values {d : ℕ} (chi : DirichletCharacter ℂ d) (n : ℕ) :
    lwdProduct (1 : DirichletCharacter ℂ 1) chi n = chi n := by
  rw [lwdProduct_apply, modOne_principal_apply, one_mul]

theorem two_principal_product_values {d : ℕ} (chi : DirichletCharacter ℂ d) (n : ℕ) :
    lwdProduct (lwdProduct (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)) chi n =
      chi n := by
  rw [lwdProduct_apply, principal_product_values, modOne_principal_apply, one_mul]

theorem principal_damped_eq (sigma t : ℝ) :
    dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK t =
      zetaDamped sigma t := by
  simp only [dampedLogDeriv, zetaDamped, DirichletCharacter.LFunction_modOne_eq]

theorem lwd_case_ii_g {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    lwdG (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) chi sigma t u v =
      zetaDamped sigma 0 + zetaDamped sigma t + zetaDamped sigma u +
        dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK v +
        zetaDamped sigma (t + u) +
        dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + v) +
        dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (u + v) +
        dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u + v) := by
  have hp (s : ℝ) := general_damped_eq_of_nat_values
    (lwdProduct (1 : DirichletCharacter ℂ 1) chi) chi
    (principal_product_values chi) hs s
  have hpp := general_damped_eq_of_nat_values
    (lwdProduct (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1))
    (1 : DirichletCharacter ℂ 1) (principal_product_values _) hs (t + u)
  have ht := general_damped_eq_of_nat_values
    (lwdProduct (lwdProduct (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)) chi)
    chi (two_principal_product_values chi) hs (t + u + v)
  simp only [lwdG, hp, hpp, ht, principal_damped_eq]

theorem primitive_height_cost {d q : ℕ} [NeZero d] [NeZero q] {x sigma t : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (ht : |t| ≤ x / q) (hs : 1 < sigma) (hs1 : sigma < 1.15) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff * Real.log x - stechkinConductorCoeff * Real.log Real.pi + 0.3918 := by
  have hh := primitive_damped_bound hc hp hs (by linarith : sigma ≤ 23 / 20) t
  have hl := mul_le_mul_of_nonneg_left (lwd_height_log hdq hq ht) conductorCoeff_bounds.1
  nlinarith only [hh, hl]

theorem lwd_2_20 {d q : ℕ} [NeZero d] [NeZero q] {x sigma t u : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (ht : |t| ≤ x / q) (hu : |u| ≤ x / q)
    (hs : 1 < sigma) (hs1 : sigma < 1.15) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u) ≤
      stechkinConductorCoeff * Real.log (2 * x) -
        stechkinConductorCoeff * Real.log Real.pi + 0.3918 := by
  have hx : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  apply primitive_height_cost hdq (show (q : ℝ) ≤ 2 * x by linarith) chi hc hp _ hs hs1
  rw [mul_div_assoc]
  linarith [abs_add_le t u]

theorem lwd_2_19 {d q : ℕ} [NeZero d] [NeZero q] {x sigma t u v : ℝ}
    (hdq : d ∣ q) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ d) (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    (ht : |t| ≤ x / q) (hu : |u| ≤ x / q) (hv : |v| ≤ x / q)
    (hs : 1 < sigma) (hs1 : sigma < 1.15) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u + v) ≤
      stechkinConductorCoeff * Real.log (3 * x) -
        stechkinConductorCoeff * Real.log Real.pi + 0.3918 := by
  have hx : 0 < x := (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q).trans_le hq
  apply primitive_height_cost hdq (show (q : ℝ) ≤ 3 * x by linarith) chi hc hp _ hs hs1
  rw [mul_div_assoc]
  linarith [abs_add_le t u, abs_add_le (t + u) v]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases
