import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralZeta

/-! The mixed principal/nonprincipal pair, with no imprimitive Euler correction left unpaid. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_zeta_single {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p : ZeroSlots 1 alpha y) (hp : p.character = 1) :
    dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK p.value.im +
      1 / (sigma - p.value.re) ≤
      stechkinConductorCoeff * (Real.log (max 1 |p.value.im|) - Real.log Real.pi) +
        23 / 40 - 11 * stechkinK / 30 := by
  have hz := mem_strictZeroValues.mp p.zero_mem
  have hh := ordinary_selected_bound (1 : DirichletCharacter ℂ 1) hs hs1 p.value.im {p.value}
    (by intro z h; simpa only [Finset.mem_singleton.mp h] using
      And.intro (ha.trans_lt hz.2.2.1) hz.2.2.2.1)
  simp only [ordinaryCost, ite_true, principalPrimeCost, Nat.primeFactors_one,
    Finset.sum_empty, add_zero, ordinaryMass, Finset.sum_singleton] at hh
  have hm : (1 : ℝ) ≤ analyticOrderNatAt (1 : DirichletCharacter ℂ 1).LFunction p.value := by
    have hi := p.index_lt
    rw [hp] at hi
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hi)
  have hk : 0 ≤ reflectedKernel sigma p.value.im p.value :=
    dampedZeroKernel_pair_nonneg hs _ ⟨hz.2.1.le, hz.2.2.2.1.le⟩
  have hd := selected_pair_dominates hs ⟨hz.2.1, hz.2.2.2.1⟩
  change _ ≤ reflectedKernel sigma p.value.im p.value at hd
  have hpole := poleDifference_high_nonpos hs hs1 (general_principal_slot_height p hp).le
  nlinarith only [hh, hm, hk, hd, hpole]

theorem general_mixed_euler {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    {sigma : ℝ} (hs : 1 < sigma) (t u : ℝ) :
    0 ≤ 2 * zetaDamped sigma 0 +
      2 * dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK t +
      2 * dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK u +
      dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (t + u) +
      dampedLogDeriv chi⁻¹ sigma (stechkinSigma sigma) stechkinK (t - u) := by
  let : NeZero (1 * d) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne d)⟩
  have he := heterolevel_pair_euler_nonneg (1 : DirichletCharacter ℂ 1) chi hs t u
  have hv (psi : DirichletCharacter ℂ d) (n : ℕ) :
      pairCharacter (1 : DirichletCharacter ℂ 1) psi n = psi n := by
    rw [pairCharacter_apply]
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one, one_mul]
  rw [general_damped_eq_of_nat_values _ _ (hv chi) hs,
    general_damped_eq_of_nat_values _ _ (hv chi⁻¹) hs] at he
  exact he

theorem general_mixed_mother {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hp : p.character = 1) (hr : r.character ≠ 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  let a := general_principal_slot hx0 p hp
  let chi := r.character
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hc := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hr
  have hc' : chi.primitiveCharacter⁻¹ ≠ 1 := inv_ne_one.mpr hc
  have hprim := chi.primitiveCharacter_isPrimitive
  have h1 := general_zeta_single hs hs1 ha a rfl
  have hz := mem_strictZeroValues.mp r.zero_mem
  have h2 := general_inducing_selected chi hr (ha.trans_lt hz.2.2.1) hz.2.2.2.1 hs hs1
  have h3 := primitive_damped_bound hc hprim hs hs1 (p.value.im + r.value.im)
  have h4 := primitive_damped_bound hc' (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hprim)
    hs hs1 (p.value.im - r.value.im)
  have he := general_mixed_euler chi.primitiveCharacter hs p.value.im r.value.im
  have h0 := zeta_real_strong hs hs1
  have hm : (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction r.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) r.index_lt)
  have hm' := div_le_div_of_nonneg_right hm (show 0 ≤ sigma - r.value.re by linarith [hz.2.2.2.1])
  change dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK p.value.im +
    1 / (sigma - p.value.re) ≤ stechkinConductorCoeff *
      (Real.log (max 1 |p.value.im|) - Real.log Real.pi) + 23 / 40 - 11 * stechkinK / 30 at h1
  have hfunction :
      1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + stechkinConductorCoeff *
        (2 * Real.log chi.conductor + Real.log (max 1 |p.value.im|) + Real.log (max 1 |r.value.im|) +
          (Real.log (max 1 |p.value.im + r.value.im|) +
            Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi) +
          43 / 120 - 11 * stechkinK / 30 := by
    linarith
  have hd : Real.log chi.conductor ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
    (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level)
  have hz0 := mem_strictZeroValues.mp p.zero_mem
  have hlp := conductor_height_log_max_le hq hz0.2.2.2.2
  have hlr := conductor_height_log_max_le hq hz.2.2.2.2
  have hls := paired_height_logs hq hz0.2.2.2.2 hz.2.2.2.2
  have hlogs : 2 * Real.log chi.conductor + Real.log (max 1 |p.value.im|) +
      Real.log (max 1 |r.value.im|) +
      (Real.log (max 1 |p.value.im + r.value.im|) +
        Real.log (max 1 |p.value.im - r.value.im|)) / 2 - 3 * Real.log Real.pi ≤
      3 * Real.log x + Real.log 2 - 3 * Real.log Real.pi := by
    linarith [hls.1, hls.2, Real.log_natCast_nonneg q]
  have hmult := mul_le_mul_of_nonneg_left hlogs conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hconst : stechkinConductorCoeff * (Real.log 2 - 3 * Real.log Real.pi) +
      43 / 120 - 11 * stechkinK / 30 ≤ 0 := by
    nlinarith only [hk, stechkinK_mem.1, LiuWang.Proof.ChebyshevBound.HighHeight.log_pi_ge_one,
      Real.log_two_lt_d9]
  nlinarith only [hfunction, hmult, hconst]

end LiuWang.Proof.MultiZeroRepulsion.Continuation
