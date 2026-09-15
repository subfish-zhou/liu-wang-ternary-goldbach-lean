import LiuWang.Proof.SourceRoute.Exception.Restart.OriginalPayment
import LiuWang.Proof.MultiZeroRepulsion.Continuation.HeterolevelEuler

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale
open LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem induced_inverse (d : PrimitiveQuadraticDatum) (q : ℕ) :
    (inducedAt d q)⁻¹ = inducedAt d q := by
  have hd : d.character⁻¹ = d.character :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using d.square_eq_one)
  unfold inducedAt
  split_ifs <;> simp [← map_inv, hd]

theorem pair_principal_forces_induction (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : pairCharacter d.character chi = 1) :
    d.modulus ∣ q ∧ inducedAt d q = chi := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let a := DirichletCharacter.changeLevel (dvd_mul_right d.modulus q) d.character
  let b := DirichletCharacter.changeLevel (dvd_mul_left q d.modulus) chi
  have ha : a * a = 1 := by
    dsimp [a]
    rw [← pow_two, ← map_pow, d.square_eq_one, map_one]
  have hab : a = b := by
    apply mul_left_cancel (a := a)
    exact ha.trans hp.symm
  have hf := DirichletCharacter.factorsThrough_gcd d.character chi hab
  have hdiv : d.modulus ∣ q := by
    have h := DirichletCharacter.conductor_dvd_of_mem_conductorSet d.character hf
    rw [d.isPrimitive] at h
    exact h.trans (Nat.gcd_dvd_right d.modulus q)
  refine ⟨hdiv, ?_⟩
  rw [inducedAt, dif_pos hdiv]
  apply DirichletCharacter.changeLevel_injective (dvd_mul_left q d.modulus)
  simpa only [← DirichletCharacter.changeLevel_trans] using hab

theorem primitive_pair_nonprincipal_of_not_induced (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hne : chi ≠ inducedAt d q) :
    pairCharacter d.character chi.primitiveCharacter ≠ 1 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  intro hp
  obtain ⟨hd, he⟩ := pair_principal_forces_induction d chi.primitiveCharacter hp
  have hdq := hd.trans chi.conductor_dvd_level
  apply hne
  rw [inducedAt, dif_pos hdq, ← chi.changeLevel_primitiveCharacter, ← he,
    inducedAt, dif_pos hd, ← DirichletCharacter.changeLevel_trans]

theorem mixed_sources_damped_bound (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hprim : chi.IsPrimitive)
    (hp : pairCharacter d.character chi ≠ 1)
    (hm : pairCharacter d.character chi⁻¹ ≠ 1)
    {beta : ℝ} {rho : ℂ} (hb : 1 / 2 < beta) (hr : 1 / 2 < rho.re)
    (hzb : datumL d (beta : ℂ) = 0) (hz : chi.LFunction rho = 0)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    1 / (sigma - beta) + 1 / (sigma - rho.re) ≤ 1 / (sigma - 1) +
      2 * stechkinConductorCoeff *
        (Real.log d.modulus + Real.log q + Real.log (max 1 |rho.im|)) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let : NeZero (d.modulus * q) := ⟨Nat.mul_ne_zero d.modulus_ne (NeZero.ne q)⟩
  have hpos := heterolevel_pair_euler_nonneg d.character chi hs 0 rho.im
  have hd := primitive_actual_selected_bound d.ne_one d.isPrimitive hb hzb hs hs1
  have he := primitive_actual_selected_bound hc hprim hr hz hs hs1
  have hplus := imprimitive_damped_bound (pairCharacter d.character chi) hp hs hs1 rho.im
  have hminus := imprimitive_damped_bound (pairCharacter d.character chi⁻¹) hm hs hs1 (-rho.im)
  have hcplus := conductor_euler_refined (pairCharacter d.character chi) hs
  have hcminus := conductor_euler_refined (pairCharacter d.character chi⁻¹) hs
  have hzet := zeta_real_strong hs hs1
  have hpi := mul_le_mul_of_nonneg_left ChebyshevBound.HighHeight.log_pi_ge_one
    conductorCoeff_bounds.1
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast d.modulus_ne)
    (by exact_mod_cast NeZero.ne q)] at hcplus hcminus
  simp only [zero_add, zero_sub] at hpos
  simp only [Complex.ofReal_im, abs_zero, max_eq_left zero_le_one, Real.log_one,
    add_zero, Complex.ofReal_re] at hd
  rw [abs_neg] at hminus
  nlinarith [conductorCoeff_lower]

theorem mixed_sources_exclusion (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] {x beta : ℝ} (hx : 10 ≤ x)
    (hdx : (d.modulus : ℝ) ≤ x) (hq : (q : ℝ) ≤ x)
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hprim : chi.IsPrimitive)
    (hp : pairCharacter d.character chi ≠ 1)
    (hm : pairCharacter d.character chi⁻¹ ≠ 1)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log x) ≤ rho.re)
    (ht : |rho.im| ≤ x / q) : chi.LFunction rho ≠ 0 := by
  intro hz
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one)
      (by simpa using le_of_not_gt h) hzb
  have hr1 : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  apply two_zero_budget_contradiction hx hb1 hr1 hb hr
  intro sigma hs hs1
  have hh := mixed_sources_damped_bound d chi hc hprim hp hm
    (original_re_half hx hb) (original_re_half hx hr) hzb hz hs hs1
  have hld := Real.log_le_log (Nat.cast_pos.mpr d.modulus_pos) hdx
  have hqt := conductor_height_log_max_le hq ht
  have hlogs := mul_le_mul_of_nonneg_left (add_le_add hld hqt)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
  nlinarith only [hh, hlogs]

end LiuWang.Proof.SourceRoute.Exception.Restart
