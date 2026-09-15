import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal.FourPhases

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.PrincipalCases

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

theorem product_damped_comm {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedLogDeriv (lwdProduct chi psi) sigma (stechkinSigma sigma) stechkinK t =
      dampedLogDeriv (lwdProduct psi chi) sigma (stechkinSigma sigma) stechkinK t := by
  apply general_damped_eq_of_nat_values _ _ _ hs
  intro n
  simp only [lwdProduct_apply, mul_comm]

theorem g_swap_first_two {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    lwdG chi psi eta sigma t u v = lwdG psi chi eta sigma u t v := by
  have h3 := general_damped_eq_of_nat_values
    (lwdProduct (lwdProduct chi psi) eta) (lwdProduct (lwdProduct psi chi) eta)
    (fun n => by simp only [lwdProduct_apply, mul_comm (chi n) (psi n)]) hs (t + u + v)
  unfold lwdG
  rw [product_damped_comm chi psi hs, h3, add_comm u t]
  ring

theorem g_swap_last_two {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) {sigma : ℝ} (hs : 1 < sigma) (t u v : ℝ) :
    lwdG chi psi eta sigma t u v = lwdG chi eta psi sigma t v u := by
  have h3 := general_damped_eq_of_nat_values
    (lwdProduct (lwdProduct chi psi) eta) (lwdProduct (lwdProduct chi eta) psi)
    (fun n => by simp only [lwdProduct_apply]; ring) hs (t + u + v)
  unfold lwdG
  rw [product_damped_comm psi eta hs, h3, add_comm v u, add_right_comm t v u]
  ring

theorem lwd_case_iii_middle {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi (1 : DirichletCharacter ℂ 1) psi (lwdSourceSigma x) tau.im rho.im upsilon.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - tau.re) + 1 / (lwdSourceSigma x - rho.re) +
          1 / (lwdSourceSigma x - upsilon.re)) +
        7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  rw [g_swap_first_two chi _ psi (lwd_source_parameters h.scale_ge).2.2.1]
  have hh := lwd_case_iii h hgammaHigh hgammaLow
  linarith only [hh]

theorem lwd_case_iii_last {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    {x : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {rho tau upsilon : ℂ} (h : CaseIIIData x q chi psi rho tau upsilon)
    (hgammaHigh : ∀ t : ℝ, 1 ≤ |t| → gammaHalfDifference (lwdSourceSigma x) t <
      stechkinConductorCoeff * Real.log |t| + 0.3316)
    (hgammaLow : ∀ t : ℝ, |t| < 1 → gammaHalfDifference (lwdSourceSigma x) t < 0.0615) :
    lwdG chi psi (1 : DirichletCharacter ℂ 1) (lwdSourceSigma x) tau.im upsilon.im rho.im ≤
      1 / (lwdSourceSigma x - 1) -
        (1 / (lwdSourceSigma x - tau.re) + 1 / (lwdSourceSigma x - upsilon.re) +
          1 / (lwdSourceSigma x - rho.re)) +
        7 * stechkinConductorCoeff * Real.log x + 1.3238 := by
  rw [g_swap_last_two chi psi _ (lwd_source_parameters h.scale_ge).2.2.1]
  have hh := lwd_case_iii_middle h hgammaHigh hgammaLow
  linarith only [hh]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal
