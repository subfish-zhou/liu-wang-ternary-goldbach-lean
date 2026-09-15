import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Products
import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts.Selection

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.SinglePrincipal

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts

theorem common_lift_primitive_LFunction {d e q : ℕ} [NeZero d] [NeZero e] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) [NeZero chi.conductor]
    (hd : d ∣ q) (he : e ∣ q) (hp : psi.IsPrimitive)
    (h : chi.changeLevel hd = psi.changeLevel he) (z : ℂ) :
    chi.primitiveCharacter.LFunction z = psi.LFunction z := by
  have hcond : chi.conductor = e := by
    have hh := congrArg DirichletCharacter.conductor h
    rwa [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel, hp] at hh
  subst e
  have hsame : chi.primitiveCharacter = psi := by
    apply DirichletCharacter.changeLevel_injective he
    have hh := congrArg (DirichletCharacter.changeLevel hd) chi.changeLevel_primitiveCharacter
    rw [← DirichletCharacter.changeLevel_trans] at hh
    exact hh.trans h
  rw [hsame]

theorem triple_pair_zero {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) [NeZero (lwdProduct chi psi).conductor]
    (hd : d ∣ q) (he : e ∣ q) (hf : f ∣ q)
    (hc : eta ≠ 1) (hp : eta.IsPrimitive)
    (hm : lwdProduct (lwdProduct chi psi) eta = 1)
    {rho : ℂ} (hz : eta.LFunction rho = 0) :
    (lwdProduct chi psi).primitiveCharacter.LFunction (conj rho) = 0 := by
  have hh := (mul_eq_one_iff_eq_inv).mp ((triple_principal_iff chi psi eta hd he hf).mp hm)
  rw [← product_changeLevel chi psi hd he, ← map_inv] at hh
  rw [common_lift_primitive_LFunction _ eta⁻¹ (Nat.lcm_dvd hd he) hf
    (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hp) hh,
    BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj hc,
    conj_conj, hz, map_zero]

theorem imprimitive_one_debit {d q : ℕ} [NeZero d] [NeZero q]
    (chi : DirichletCharacter ℂ d) [NeZero chi.conductor]
    (hc : chi ≠ 1) {x sigma t : ℝ} (hd : d ∣ q) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 1.02) (hy : |t| ≤ x / q)
    {rho : ℂ} (hr : 1 / 2 < rho.re ∧ rho.re < 1)
    (hg : 1 - rho.re ≤ sigma - 1) (hz : chi.primitiveCharacter.LFunction rho = 0) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      nonprincipalCost x + 0.4977 - poleDebit sigma rho.re (t - rho.im) := by
  have hp := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hm := primitive_selected_reflections chi.primitiveCharacter hp chi.primitiveCharacter_isPrimitive hs t {rho}
    (by simpa only [Finset.mem_singleton, forall_eq] using hr)
    (by simpa only [Finset.mem_singleton, forall_eq] using hz)
  simp only [Finset.sum_singleton] at hm
  have hk := poleDebit_le_reflected hs hs1 hr.1 hr.2 hg t
  have hb := imprimitive_full_zero_sum_bound chi hc hs (by linarith : sigma ≤ 23 / 20) t
  have he := lwd_2_9 chi hs
  have hl := mul_le_mul_of_nonneg_left (lwd_height_log hd hq hy) conductorCoeff_bounds.1
  unfold nonprincipalCost
  nlinarith only [hm, hk, hb, he, hl]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.NonprincipalProducts
