import LiuWang.Proof.MultiZeroRepulsion.Continuation.HeterolevelEuler
import LiuWang.Proof.NearOneDensity.Continuation.MixedPhase

/-! The actual heterolevel Euler products transported to lcm and the original fixed modulus. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_damped_eq_of_nat_values {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (he : ∀ n : ℕ, chi n = psi n) {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t =
      dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK t := by
  have hterm (a : ℝ) : eulerTerm chi a t = eulerTerm psi a t := by
    funext n
    by_cases hn : n = 0
    · simp [eulerTerm, hn]
    · simp only [eulerTerm, LSeries.term_of_ne_zero hn, Pi.mul_apply, he n]
  have h1 := (eulerTerm_hasSum chi hs t).unique ((hterm sigma).symm ▸ eulerTerm_hasSum psi hs t)
  have h2 := (eulerTerm_hasSum chi (hs.trans_le (stechkinSigma_ge hs)) t).unique
    ((hterm (stechkinSigma sigma)).symm ▸ eulerTerm_hasSum psi (hs.trans_le (stechkinSigma_ge hs)) t)
  unfold dampedLogDeriv
  rw [h1, neg_inj.mp h2]

theorem general_lcm_euler {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    {sigma : ℝ} (hs : 1 < sigma) (t u : ℝ) :
    0 ≤ 2 * zetaDamped sigma 0 +
      2 * dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t +
      2 * dampedLogDeriv psi sigma (stechkinSigma sigma) stechkinK u +
      dampedLogDeriv (mixedQuotient chi psi⁻¹) sigma (stechkinSigma sigma) stechkinK (t + u) +
      dampedLogDeriv (mixedQuotient chi psi) sigma (stechkinSigma sigma) stechkinK (t - u) := by
  let : NeZero (d * e) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne e)⟩
  have hp : ∀ n : ℕ, pairCharacter chi psi n = mixedQuotient chi psi⁻¹ n := by
    intro n
    rw [pairCharacter_apply, mixedQuotient_nat_apply,
      BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply, inv_inv]
  have hm : ∀ n : ℕ, pairCharacter chi psi⁻¹ n = mixedQuotient chi psi n := by
    intro n
    rw [pairCharacter_apply, mixedQuotient_nat_apply,
      BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply]
  have he := heterolevel_pair_euler_nonneg chi psi hs t u
  rw [general_damped_eq_of_nat_values _ _ hp hs, general_damped_eq_of_nat_values _ _ hm hs] at he
  exact he

theorem general_inducing_product_ne_one {q : ℕ} [NeZero q]
    (chi psi : DirichletCharacter ℂ q) [NeZero chi.conductor] [NeZero psi.conductor]
    (hprod : chi * psi ≠ 1) :
    mixedQuotient chi.primitiveCharacter psi.primitiveCharacter⁻¹ ≠ 1 := by
  intro he
  have hh := mixed_quotient_changeLevel chi.primitiveCharacter psi.primitiveCharacter⁻¹
    chi.conductor_dvd_level psi.conductor_dvd_level
  rw [he, map_one, map_inv, DirichletCharacter.changeLevel_primitiveCharacter,
    DirichletCharacter.changeLevel_primitiveCharacter] at hh
  change 1 = chi * star psi⁻¹ at hh
  rw [MulChar.star_eq_inv, inv_inv] at hh
  exact hprod hh.symm

end LiuWang.Proof.MultiZeroRepulsion.Continuation
