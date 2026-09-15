import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Transport

/-! The genuine principal triple product, with inverse-third-slot kernels paying its pole. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_principal_lcm_cost {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    {x sigma t : ℝ} (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    (ht : |t| ≤ 3 * x / q) :
    dampedLogDeriv (1 : DirichletCharacter ℂ d) sigma (stechkinSigma sigma) stechkinK t ≤
      poleDifference sigma t +
      stechkinConductorCoeff * (Real.log x + Real.log 3 - Real.log Real.pi) +
      23 / 40 - 11 * stechkinK / 30 + 941 / 1600 := by
  have hh := principal_all_height (q := d) hs hs1 t
  have hP := t1_principal_prime_cost (q := d) hs hs1
  have hl := t1_height_log hd hq (by norm_num : (1 : ℝ) ≤ 3) ht
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  linarith

theorem t1G_principal_triple_bound {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) (ha : 9 / 10 ≤ alpha)
    (p r s : ZeroSlots q alpha (x / q))
    [NeZero p.character.conductor] [NeZero r.character.conductor] [NeZero s.character.conductor]
    (hp : p.character ≠ 1) (hr : r.character ≠ 1) (hsc : s.character ≠ 1)
    (htriple : p.character * r.character * s.character = 1)
    (hgr : 1 - r.value.re ≤ sigma - 1)
    (hgs : 1 - s.value.re ≤ sigma - 1) :
    t1G p.character.primitiveCharacter r.character.primitiveCharacter s.character.primitiveCharacter
      sigma p.value.im r.value.im s.value.im +
      (analyticOrderNatAt p.character.LFunction p.value : ℝ) / (sigma - p.value.re) +
      (analyticOrderNatAt r.character.LFunction r.value : ℝ) / (sigma - r.value.re) +
      (analyticOrderNatAt s.character.LFunction s.value : ℝ) / (sigma - s.value.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 12 / 5 := by
  let chi := p.character.primitiveCharacter
  let psi := r.character.primitiveCharacter
  let eta := s.character.primitiveCharacter
  have hd := p.character.conductor_dvd_level
  have he := r.character.conductor_dvd_level
  have hf := s.character.conductor_dvd_level
  have hl1 : chi.changeLevel hd = p.character := DirichletCharacter.changeLevel_primitiveCharacter _
  have hl2 : psi.changeLevel he = r.character := DirichletCharacter.changeLevel_primitiveCharacter _
  have hl3 : eta.changeLevel hf = s.character := DirichletCharacter.changeLevel_primitiveCharacter _
  have hs15 : sigma ≤ 23 / 20 := by linarith
  have ha5 : 1 / 2 ≤ alpha := by linarith
  have htuple : chi.changeLevel hd * psi.changeLevel he * eta.changeLevel hf = 1 := by
    rwa [hl1, hl2, hl3]
  have htuple' : chi.changeLevel hd * eta.changeLevel hf * psi.changeLevel he = 1 := by
    rw [show chi.changeLevel hd * eta.changeLevel hf * psi.changeLevel he =
      chi.changeLevel hd * psi.changeLevel he * eta.changeLevel hf by ac_rfl]
    exact htuple
  have htriple' : t1Product (t1Product chi psi) eta = 1 := by
    apply DirichletCharacter.changeLevel_injective (Nat.lcm_dvd (Nat.lcm_dvd hd he) hf)
    rw [map_one, t1Product_changeLevel _ _ (Nat.lcm_dvd hd he) hf,
      t1Product_changeLevel chi psi hd he]
    exact htuple
  have hpair : t1Product psi eta ≠ 1 := by
    intro hh
    have h := t1Product_changeLevel psi eta he hf
    rw [hh, map_one, hl2, hl3] at h
    have hc : p.character = 1 := by
      simpa only [mul_assoc, ← h, mul_one] using htriple
    exact hp hc
  have zp := mem_strictZeroValues.mp p.zero_mem
  have zr := mem_strictZeroValues.mp r.zero_mem
  have zs := mem_strictZeroValues.mp s.zero_mem
  have h0 := zeta_real_strong hs hs15
  have h1 := general_inducing_selected p.character hp (ha5.trans_lt zp.2.2.1) zp.2.2.2.1 hs hs15
  have h2 := general_inducing_selected r.character hr (ha5.trans_lt zr.2.2.1) zr.2.2.2.1 hs hs15
  have h3 := general_inducing_selected s.character hsc (ha5.trans_lt zs.2.2.1) zs.2.2.2.1 hs hs15
  have h4 := t1_triple_principal_selected chi psi eta hd he hf hs hs15 ha5 s hl3 hsc htuple
    (p.value.im + r.value.im)
  have h5 := t1_triple_principal_selected chi eta psi hd hf he hs hs15 ha5 r hl2 hr htuple'
    (p.value.im + s.value.im)
  have h6 := general_nonprincipal_cost (t1Product psi eta) hpair hs hs15 (r.value.im + s.value.im)
  have h7 : dampedLogDeriv (t1Product (t1Product chi psi) eta)
      sigma (stechkinSigma sigma) stechkinK (p.value.im + r.value.im + s.value.im) ≤
      poleDifference sigma (p.value.im + r.value.im + s.value.im) +
      stechkinConductorCoeff * (Real.log x + Real.log 3 - Real.log Real.pi) +
      23 / 40 - 11 * stechkinK / 30 + 941 / 1600 := by
    rw [htriple']
    apply t1_principal_lcm_cost (Nat.lcm_dvd (Nat.lcm_dvd hd he) hf) hq hs hs15
    have hab := (t1_pair_height zp.2.2.2.2 zr.2.2.2.2).1
    have hh := abs_add_le (p.value.im + r.value.im) s.value.im
    rw [mul_div_assoc] at hab ⊢
    linarith [zs.2.2.2.2]
  have hpay := t1_two_kernels_pay_pole hs hs1
    (rho := conj s.value) (tau := conj r.value)
    (ha.trans zs.2.2.1.le) zs.2.2.2.1 (ha.trans zr.2.2.1.le) zr.2.2.2.1 hgs hgr
    (t := p.value.im + r.value.im) (u := p.value.im + s.value.im)
    (v := p.value.im + r.value.im + s.value.im)
    (by simp) (by simp only [conj_im, sub_neg_eq_add]; ring)
  have l1 := t1_height_log hd hq (le_refl (1 : ℝ)) (by simpa using zp.2.2.2.2)
  have l2 := t1_height_log he hq (le_refl (1 : ℝ)) (by simpa using zr.2.2.2.2)
  have l3 := t1_height_log hf hq (le_refl (1 : ℝ)) (by simpa using zs.2.2.2.2)
  simp only [Real.log_one, add_zero] at l1 l2 l3
  have l4 := t1_height_log (Nat.lcm_dvd hd he) hq (by norm_num : (1 : ℝ) ≤ 2)
    (t1_pair_height zp.2.2.2.2 zr.2.2.2.2).1
  have l5 := t1_height_log (Nat.lcm_dvd hd hf) hq (by norm_num : (1 : ℝ) ≤ 2)
    (t1_pair_height zp.2.2.2.2 zs.2.2.2.2).1
  have l6 := t1_height_log (Nat.lcm_dvd he hf) hq (by norm_num : (1 : ℝ) ≤ 2)
    (t1_pair_height zr.2.2.2.2 zs.2.2.2.2).1
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add l1 l2) l3) l4) l5) l6)
    conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hconst : stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) +
      6 * (4 / 15 : ℝ) + (23 / 40 - 11 * stechkinK / 30) + 4 * (941 / 1600) - 3 / 4 ≤ 12 / 5 := by
    nlinarith only [hk, stechkinK_ge, Real.log_two_lt_d9, Real.log_three_lt_d9,
      LiuWang.Proof.NearOneDensity.log_pi_ge_eleven_tenths]
  unfold t1G
  linear_combination h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + hpay + hm + hconst

end LiuWang.Proof.MultiZeroRepulsion.Continuation
