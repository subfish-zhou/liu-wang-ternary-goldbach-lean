import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralEulerCost
import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralLcm
import LiuWang.Proof.MultiZeroRepulsion.Continuation.PrimitiveCount

/-! The actual ordinary nonprincipal two-point mother at one fixed original modulus. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_inducing_selected {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor] (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    dampedLogDeriv chi.primitiveCharacter sigma (stechkinSigma sigma) stechkinK rho.im +
      (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) ≤
      stechkinConductorCoeff *
        (Real.log chi.conductor + Real.log (max 1 |rho.im|) - Real.log Real.pi) + 4 / 15 := by
  rw [analyticOrderNatAt_LFunction_eq_primitive chi hc (by linarith)]
  exact primitive_multiplicity_bound
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc)
    chi.primitiveCharacter_isPrimitive hr hr1 hs hs1

theorem general_distinct_pair_function {q : ℕ} [NeZero q]
    (chi psi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hd : psi ≠ 1)
    (hm : chi * psi ≠ 1) (hi : chi ≠ psi)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) +
      (analyticOrderNatAt psi.LFunction tau : ℝ) / (sigma - tau.re) ≤
      1 / (sigma - 1) + stechkinConductorCoeff *
        (Real.log chi.conductor + Real.log psi.conductor +
          Real.log (Nat.lcm chi.conductor psi.conductor) +
          Real.log (max 1 |rho.im|) + Real.log (max 1 |tau.im|) +
          (Real.log (max 1 |rho.im + tau.im|) + Real.log (max 1 |rho.im - tau.im|)) / 2 -
          3 * Real.log Real.pi) + 1021 / 1600 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let : NeZero psi.conductor := ⟨psi.conductor_ne_zero⟩
  have he := general_lcm_euler chi.primitiveCharacter psi.primitiveCharacter hs rho.im tau.im
  have h0 := zeta_real_strong hs hs1
  have h1 := general_inducing_selected chi hc hr hr1 hs hs1
  have h2 := general_inducing_selected psi hd ht ht1 hs hs1
  have h3 := general_nonprincipal_cost (mixedQuotient chi.primitiveCharacter psi.primitiveCharacter⁻¹)
    (general_inducing_product_ne_one chi psi hm) hs hs1 (rho.im + tau.im)
  have h4 := general_nonprincipal_cost (mixedQuotient chi.primitiveCharacter psi.primitiveCharacter)
    (inducing_mixed_ne_one hi) hs hs1 (rho.im - tau.im)
  linarith

theorem general_distinct_pair_global {q : ℕ} [NeZero q] {x : ℝ} (hq : (q : ℝ) ≤ x)
    (chi psi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hd : psi ≠ 1)
    (hm : chi * psi ≠ 1) (hi : chi ≠ psi)
    {rho tau : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1)
    (hry : |rho.im| ≤ x / q) (hty : |tau.im| ≤ x / q)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) +
      (analyticOrderNatAt psi.LFunction tau : ℝ) / (sigma - tau.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  have hh := general_distinct_pair_function chi psi hc hd hm hi hr hr1 ht ht1 hs hs1
  have hdc : Real.log chi.conductor ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
    (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level)
  have hdp : Real.log psi.conductor ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero psi.conductor_ne_zero)
    (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) psi.conductor_dvd_level)
  have hlcm : Real.log (Nat.lcm chi.conductor psi.conductor) ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero chi.conductor_ne_zero psi.conductor_ne_zero))
    (by exact_mod_cast (Nat.le_of_dvd (NeZero.pos q)
      (Nat.lcm_dvd chi.conductor_dvd_level psi.conductor_dvd_level)))
  have hl1 := conductor_height_log_max_le hq hry
  have hl2 := conductor_height_log_max_le hq hty
  have hl3 := paired_height_logs hq hry hty
  have hlog : Real.log chi.conductor + Real.log psi.conductor +
      Real.log (Nat.lcm chi.conductor psi.conductor) +
      Real.log (max 1 |rho.im|) + Real.log (max 1 |tau.im|) +
      (Real.log (max 1 |rho.im + tau.im|) + Real.log (max 1 |rho.im - tau.im|)) / 2 -
      3 * Real.log Real.pi ≤ 3 * Real.log x + Real.log 2 - 3 * Real.log Real.pi := by
    linarith [hl3.1, hl3.2]
  have hmult := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hpi := LiuWang.Proof.NearOneDensity.log_pi_ge_eleven_tenths
  have htwo := Real.log_two_lt_d9
  have hconst : stechkinConductorCoeff * (Real.log 2 - 3 * Real.log Real.pi) + 1021 / 1600 ≤ 0 := by
    nlinarith only [hk, hpi, htwo]
  nlinarith only [hh, hmult, hconst]

theorem general_slots_labels {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character ≠ 1) (hd : r.character ≠ 1) :
    p.character = r.character ∨ p.character = r.character⁻¹ := by
  by_contra hn
  have hm : p.character * r.character ≠ 1 :=
    fun he => hn (Or.inr (mul_eq_one_iff_eq_inv.mp he))
  have hi : p.character ≠ r.character := fun he => hn (Or.inl he)
  obtain ⟨hs, hs1, ha, _⟩ := sourceSigma_parameters hx
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hh := general_distinct_pair_global hq p.character r.character hc hd hm hi
    (ha.trans_lt hp.2.2.1) hp.2.2.2.1 (ha.trans_lt hr.2.2.1) hr.2.2.2.1
    hp.2.2.2.2 hr.2.2.2.2 hs hs1
  have hmp : (1 : ℝ) ≤ analyticOrderNatAt p.character.LFunction p.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) p.index_lt)
  have hmr : (1 : ℝ) ≤ analyticOrderNatAt r.character.LFunction r.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) r.index_lt)
  have h1 := div_le_div_of_nonneg_right hmp (show 0 ≤ sourceSigma x - p.value.re by linarith [hp.2.2.2.1])
  have h2 := div_le_div_of_nonneg_right hmr (show 0 ≤ sourceSigma x - r.value.re by linarith [hr.2.2.2.1])
  have hl := source_reciprocal_sum_strict hx hp.2.2.1 hp.2.2.2.1 hr.2.2.1 hr.2.2.2.1
  linarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
