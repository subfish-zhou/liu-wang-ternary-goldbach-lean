import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Independent

/-! A repeated/inverse ordinary pair and a third character: the actual principal pair pole is retained and paid. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_source_two_selected {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha y) [NeZero p.character.conductor]
    (hc : p.character ≠ 1) (hne : p ≠ r) (hchar : r.character = p.character) (t : ℝ) :
    dampedLogDeriv p.character.primitiveCharacter sigma (stechkinSigma sigma) stechkinK t +
      reflectedKernel sigma t p.value + reflectedKernel sigma t r.value ≤
      stechkinConductorCoeff *
        (Real.log p.character.conductor + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 := by
  have hh := t1_source_slots_bound p.character hc hs hs1 ha t {p, r} (by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]
    · rw [Finset.mem_singleton.mp h]
      exact hchar)
  simpa only [Finset.sum_insert (show p ∉ ({r} : Finset _) by simpa only [Finset.mem_singleton] using hne),
    Finset.sum_singleton, add_assoc] using hh

theorem t1_principal_lcm_pair_cost {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    {x sigma t : ℝ} (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    (ht : |t| ≤ 2 * x / q) :
    dampedLogDeriv (1 : DirichletCharacter ℂ d) sigma (stechkinSigma sigma) stechkinK t ≤
      poleDifference sigma t +
      stechkinConductorCoeff * (Real.log x + Real.log 2 - Real.log Real.pi) +
      23 / 40 - 11 * stechkinK / 30 + 941 / 1600 := by
  have hh := principal_all_height (q := d) hs hs1 t
  have hP := t1_principal_prime_cost (q := d) hs hs1
  have hl := t1_height_log hd hq (by norm_num : (1 : ℝ) ≤ 2) ht
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  linarith

theorem t1SourceG_repeated_pair_bound {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) (ha : 9 / 10 ≤ alpha)
    (p r s : ZeroSlots q alpha (x / q)) (hp : p.character ≠ 1)
    (hr : r.character ≠ 1) (hsc : s.character ≠ 1)
    (hpr : p.character * r.character = 1) (hps : p.character * s.character ≠ 1)
    (hrs : r.character * s.character ≠ 1) (hnc : p ≠ conjugateSlot r)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    t1SourceG p.character r.character s.character sigma p.value.im r.value.im s.value.im +
      1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) + 1 / (sigma - s.value.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 12 / 5 := by
  let : NeZero p.character.conductor := ⟨p.character.conductor_ne_zero⟩
  let : NeZero r.character.conductor := ⟨r.character.conductor_ne_zero⟩
  let : NeZero s.character.conductor := ⟨s.character.conductor_ne_zero⟩
  let chi := p.character.primitiveCharacter
  let psi := r.character.primitiveCharacter
  let eta := s.character.primitiveCharacter
  have hd := p.character.conductor_dvd_level
  have he := r.character.conductor_dvd_level
  have hf := s.character.conductor_dvd_level
  have hde := t1Product_changeLevel chi psi hd he
  have hdf := t1Product_changeLevel chi eta hd hf
  have hef := t1Product_changeLevel psi eta he hf
  have hdef := t1Product_changeLevel (t1Product chi psi) eta (Nat.lcm_dvd hd he) hf
  rw [hde] at hdef
  simp only [chi, psi, eta, DirichletCharacter.changeLevel_primitiveCharacter] at hde hdf hef hdef
  have hde' : t1Product chi psi = 1 := by
    apply DirichletCharacter.changeLevel_injective (Nat.lcm_dvd hd he)
    rw [map_one, hde, hpr]
  have hn {d : ℕ} (chi : DirichletCharacter ℂ d) (hd : d ∣ q)
      (hn : chi.changeLevel hd ≠ 1) : chi ≠ 1 := by
    intro hh
    exact hn (by rw [hh, map_one])
  have hdf' := hn _ (Nat.lcm_dvd hd hf) (by rwa [hdf])
  have hef' := hn _ (Nat.lcm_dvd he hf) (by rwa [hef])
  have hdef' := hn (t1Product (t1Product chi psi) eta) (Nat.lcm_dvd (Nat.lcm_dvd hd he) hf)
    (by
      dsimp only [chi, psi, eta]
      rw [hdef, hpr, one_mul]
      exact hsc)
  have ha5 : 1 / 2 ≤ alpha := by linarith
  have hs15 : sigma ≤ 23 / 20 := by linarith
  have hcr : (conjugateSlot r).character = p.character := by
    rw [conjugateSlot_character]
    exact (mul_eq_one_iff_eq_inv.mp hpr).symm
  have hcp : (conjugateSlot p).character = r.character := by
    rw [conjugateSlot_character]
    exact (mul_eq_one_iff_eq_inv.mp (by rwa [mul_comm] : r.character * p.character = 1)).symm
  have h1 := t1_source_two_selected hs hs15 ha5 p (conjugateSlot r) hp hnc hcr p.value.im
  have h2 := t1_source_two_selected hs hs15 ha5 r (conjugateSlot p) hr (t1_conjugate_ne hnc) hcp r.value.im
  rw [conjugateSlot_value] at h1 h2
  have zp := mem_strictZeroValues.mp p.zero_mem
  have zr := mem_strictZeroValues.mp r.zero_mem
  have zs := mem_strictZeroValues.mp s.zero_mem
  have h3 := general_inducing_selected s.character hsc (ha5.trans_lt zs.2.2.1) zs.2.2.2.1 hs hs15
  have h3m : (1 : ℝ) ≤ analyticOrderNatAt s.character.LFunction s.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) s.index_lt)
  have h3m' := div_le_div_of_nonneg_right h3m (show 0 ≤ sigma - s.value.re by linarith [zs.2.2.2.1])
  have k1 : 1 / (sigma - p.value.re) ≤ reflectedKernel sigma p.value.im p.value :=
    selected_pair_dominates hs ⟨zp.2.1, zp.2.2.2.1⟩
  have k2 : 1 / (sigma - r.value.re) ≤ reflectedKernel sigma r.value.im r.value :=
    selected_pair_dominates hs ⟨zr.2.1, zr.2.2.2.1⟩
  have h0 := zeta_real_strong hs hs15
  have h4 := t1_principal_lcm_pair_cost (Nat.lcm_dvd hd he) hq hs hs15
    (t1_pair_height zp.2.2.2.2 zr.2.2.2.2).1
  have h5 := general_nonprincipal_cost (t1Product chi eta) hdf' hs hs15 (p.value.im + s.value.im)
  have h6 := general_nonprincipal_cost (t1Product psi eta) hef' hs hs15 (r.value.im + s.value.im)
  have h7 := general_nonprincipal_cost (t1Product (t1Product chi psi) eta) hdef' hs hs15
    (p.value.im + r.value.im + s.value.im)
  have hpay := t1_two_kernels_pay_pole hs hs1 (rho := conj r.value) (tau := conj p.value)
    (ha.trans zr.2.2.1.le) zr.2.2.2.1 (ha.trans zp.2.2.1.le) zp.2.2.2.1 hgr hgp
    (t := p.value.im) (u := r.value.im) (v := p.value.im + r.value.im)
    (by simp) (by simp [add_comm])
  have l1 := t1_height_log hd hq (le_refl (1 : ℝ)) (by simpa using zp.2.2.2.2)
  have l2 := t1_height_log he hq (le_refl (1 : ℝ)) (by simpa using zr.2.2.2.2)
  have l3 := t1_height_log hf hq (le_refl (1 : ℝ)) (by simpa using zs.2.2.2.2)
  simp only [Real.log_one, add_zero] at l1 l2 l3
  have l5 := t1_height_log (Nat.lcm_dvd hd hf) hq (by norm_num : (1 : ℝ) ≤ 2)
    (t1_pair_height zp.2.2.2.2 zs.2.2.2.2).1
  have l6 := t1_height_log (Nat.lcm_dvd he hf) hq (by norm_num : (1 : ℝ) ≤ 2)
    (t1_pair_height zr.2.2.2.2 zs.2.2.2.2).1
  have ht : |p.value.im + r.value.im + s.value.im| ≤ 3 * x / q := by
    have hab := (t1_pair_height zp.2.2.2.2 zr.2.2.2.2).1
    have hh := abs_add_le (p.value.im + r.value.im) s.value.im
    rw [mul_div_assoc] at hab ⊢
    linarith [zs.2.2.2.2]
  have l7 := t1_height_log (Nat.lcm_dvd (Nat.lcm_dvd hd he) hf) hq
    (by norm_num : (1 : ℝ) ≤ 3) ht
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add l1 l2) l3) l5) l6) l7)
    conductorCoeff_bounds.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hconst : stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) +
      6 * (4 / 15 : ℝ) + (23 / 40 - 11 * stechkinK / 30) + 4 * (941 / 1600) - 3 / 4 ≤ 12 / 5 := by
    nlinarith only [hk, stechkinK_ge, Real.log_two_lt_d9, Real.log_three_lt_d9,
      LiuWang.Proof.NearOneDensity.log_pi_ge_eleven_tenths]
  change t1G chi psi eta _ _ _ _ + _ + _ + _ ≤ _
  unfold t1G
  rw [hde'] at h7 ⊢
  linear_combination h0 + h1 + h2 + h3 + h3m' + k1 + k2 + h4 + h5 + h6 + h7 + hpay + hm + hconst

end LiuWang.Proof.MultiZeroRepulsion.Continuation
