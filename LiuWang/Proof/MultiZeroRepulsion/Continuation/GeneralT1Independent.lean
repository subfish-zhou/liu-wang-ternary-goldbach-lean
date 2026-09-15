import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Signs

/-! Four-sign ordinary three-point contradiction, now including every principal triple product. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1SourceG_pair_regular_bound {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) (ha : 9 / 10 ≤ alpha)
    (p r s : ZeroSlots q alpha (x / q)) (hp : p.character ≠ 1)
    (hr : r.character ≠ 1) (hsc : s.character ≠ 1)
    (hpr : p.character * r.character ≠ 1) (hps : p.character * s.character ≠ 1)
    (hrs : r.character * s.character ≠ 1)
    (hgr : 1 - r.value.re ≤ sigma - 1) (hgs : 1 - s.value.re ≤ sigma - 1) :
    t1SourceG p.character r.character s.character sigma p.value.im r.value.im s.value.im +
      (analyticOrderNatAt p.character.LFunction p.value : ℝ) / (sigma - p.value.re) +
      (analyticOrderNatAt r.character.LFunction r.value : ℝ) / (sigma - r.value.re) +
      (analyticOrderNatAt s.character.LFunction s.value : ℝ) / (sigma - s.value.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 12 / 5 := by
  let : NeZero p.character.conductor := ⟨p.character.conductor_ne_zero⟩
  let : NeZero r.character.conductor := ⟨r.character.conductor_ne_zero⟩
  let : NeZero s.character.conductor := ⟨s.character.conductor_ne_zero⟩
  by_cases ht : p.character * r.character * s.character = 1
  · exact t1G_principal_triple_bound hq hs hs1 ha p r s hp hr hsc ht hgr hgs
  · let chi := p.character.primitiveCharacter
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
    have hn {d : ℕ} (chi : DirichletCharacter ℂ d) (hd : d ∣ q)
        (hn : chi.changeLevel hd ≠ 1) : chi ≠ 1 := by
      intro hh
      exact hn (by rw [hh, map_one])
    have hde' := hn _ (Nat.lcm_dvd hd he) (by rwa [hde])
    have hdf' := hn _ (Nat.lcm_dvd hd hf) (by rwa [hdf])
    have hef' := hn _ (Nat.lcm_dvd he hf) (by rwa [hef])
    have hdef' := hn _ (Nat.lcm_dvd (Nat.lcm_dvd hd he) hf) (by rwa [hdef])
    have zp := mem_strictZeroValues.mp p.zero_mem
    have zr := mem_strictZeroValues.mp r.zero_mem
    have zs := mem_strictZeroValues.mp s.zero_mem
    have ha5 : 1 / 2 ≤ alpha := by linarith
    have hh := t1G_primitive_bound chi psi eta
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one _ hp)
      p.character.primitiveCharacter_isPrimitive
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one _ hr)
      r.character.primitiveCharacter_isPrimitive
      (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one _ hsc)
      s.character.primitiveCharacter_isPrimitive hde' hdf' hef' hdef' hd he hf hq hs
      (by linarith : sigma ≤ 23 / 20) (ha5.trans_lt zp.2.2.1) zp.2.2.2.1
      (ha5.trans_lt zr.2.2.1) zr.2.2.2.1 (ha5.trans_lt zs.2.2.1) zs.2.2.2.1
      zp.2.2.2.2 zr.2.2.2.2 zs.2.2.2.2
    rw [← analyticOrderNatAt_LFunction_eq_primitive p.character hp zp.2.1,
      ← analyticOrderNatAt_LFunction_eq_primitive r.character hr zr.2.1,
      ← analyticOrderNatAt_LFunction_eq_primitive s.character hsc zs.2.1] at hh
    change t1G chi psi eta _ _ _ _ + _ + _ + _ ≤ _
    linarith

theorem t1_scalar_twelve_fifths {x beta gamma delta : ℝ} (hx : 8000000000 ≤ x)
    (hb : 1 - (26213 / 100000) / Real.log x < beta) (hb1 : beta < 1)
    (hg : 1 - (26213 / 100000) / Real.log x < gamma) (hg1 : gamma < 1)
    (hd : 1 - (26213 / 100000) / Real.log x < delta) (hd1 : delta < 1) :
    1 / (t1Sigma x - 1) + 7 * stechkinConductorCoeff * Real.log x + 12 / 5 <
      1 / (t1Sigma x - beta) + 1 / (t1Sigma x - gamma) + 1 / (t1Sigma x - delta) := by
  have hL := source_log_twenty_two hx
  have hL0 : 0 < Real.log x := by linarith
  have hs := (t1Sigma_parameters hx).1
  have he : (t1Sigma x - 1) * Real.log x = 9 / 25 := by
    dsimp [t1Sigma]
    field_simp
    ring
  have hl {b : ℝ} (h : 1 - (26213 / 100000) / Real.log x < b) (h1 : b < 1) :
      Real.log x / (62213 / 100000) < 1 / (t1Sigma x - b) := by
    have hh : (1 - b) * Real.log x < 26213 / 100000 := by
      apply (lt_div_iff₀ hL0).mp
      linarith
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).mpr
    nlinarith
  have hl1 := hl hb hb1
  have hl2 := hl hg hg1
  have hl3 := hl hd hd1
  have hi : 1 / (t1Sigma x - 1) = Real.log x / (9 / 25) := by
    dsimp [t1Sigma]
    field_simp
    ring
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  rw [hi]
  norm_num [div_eq_mul_inv] at hl1 hl2 hl3 hk ⊢
  nlinarith only [hl1, hl2, hl3, hk, hL]

theorem t1_ordinary_pair_regular_impossible {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q))
    (hp : p.character ≠ 1) (hr : r.character ≠ 1) (hs : s.character ≠ 1)
    (hproducts : ∀ b c : Bool,
      p.character * t1Orient r.character b ≠ 1 ∧
      p.character * t1Orient s.character c ≠ 1 ∧
      t1Orient r.character b * t1Orient s.character c ≠ 1) : False := by
  have hsig := t1Sigma_parameters hx
  have hsmall := t1_source_pole_domain hx
  have hG (b c : Bool) :=
    t1SourceG_pair_regular_bound hq hsig.1 hsmall.1 hsmall.2 p (t1OrientSlot r b) (t1OrientSlot s c)
      hp (by rw [t1OrientSlot_character]; exact t1Orient_ne_one hr b)
      (by rw [t1OrientSlot_character]; exact t1Orient_ne_one hs c)
      (by rw [t1OrientSlot_character]; exact (hproducts b c).1)
      (by rw [t1OrientSlot_character]; exact (hproducts b c).2.1)
      (by rw [t1OrientSlot_character, t1OrientSlot_character]; exact (hproducts b c).2.2)
      (by have hh := mem_strictZeroValues.mp (t1OrientSlot r b).zero_mem; linarith [hsig.2.2.2, hh.2.2.1])
      (by have hh := mem_strictZeroValues.mp (t1OrientSlot s c).zero_mem; linarith [hsig.2.2.2, hh.2.2.1])
  have h00 := hG false false
  have h10 := hG true false
  have h01 := hG false true
  have h11 := hG true true
  simp only [t1OrientSlot, Bool.false_eq_true, if_false, if_true] at h00 h10 h01 h11
  have zp := mem_strictZeroValues.mp p.zero_mem
  have zr := mem_strictZeroValues.mp r.zero_mem
  have zs := mem_strictZeroValues.mp s.zero_mem
  have he := t1SourceG_four_nonneg p r s hsig.1
  simp only [conjugateSlot_character, conjugateSlot_value, conj_re,
    ordinary_order_conjugate r.character zr.2.1 zr.2.2.2.1,
    ordinary_order_conjugate s.character zs.2.1 zs.2.2.2.1] at h10 h01 h11 he
  have h1 : (1 : ℝ) ≤ analyticOrderNatAt p.character.LFunction p.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) p.index_lt)
  have h2 : (1 : ℝ) ≤ analyticOrderNatAt r.character.LFunction r.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) r.index_lt)
  have h3 : (1 : ℝ) ≤ analyticOrderNatAt s.character.LFunction s.value := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) s.index_lt)
  have h1' := div_le_div_of_nonneg_right h1 (show 0 ≤ t1Sigma x - p.value.re by linarith [hsig.1, zp.2.2.2.1])
  have h2' := div_le_div_of_nonneg_right h2 (show 0 ≤ t1Sigma x - r.value.re by linarith [hsig.1, zr.2.2.2.1])
  have h3' := div_le_div_of_nonneg_right h3 (show 0 ≤ t1Sigma x - s.value.re by linarith [hsig.1, zs.2.2.2.1])
  have hstrict := t1_scalar_twelve_fifths hx zp.2.2.1 zp.2.2.2.1 zr.2.2.1 zr.2.2.2.1 zs.2.2.1 zs.2.2.2.1
  linarith only [h00, h10, h01, h11, he, h1', h2', h3', hstrict]

theorem t1_product_five_forces_principal_or_repeated {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hcount : 4 < ∑ rho ∈ productZeroValues q (1 - (26213 / 100000) / Real.log x) (x / q),
      analyticOrderNatAt (productL q) rho) :
    ∃ p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q),
      (p ≠ r ∧ p ≠ conjugateSlot r ∧ p ≠ s ∧ p ≠ conjugateSlot s ∧
        r ≠ s ∧ r ≠ conjugateSlot s) ∧
      (p.character = 1 ∨ r.character = 1 ∨ s.character = 1 ∨
        ∃ b c : Bool, p.character * t1Orient r.character b = 1 ∨
          p.character * t1Orient s.character c = 1 ∨
          t1Orient r.character b * t1Orient s.character c = 1) ∧
      ¬(p.character ≠ 1 ∧ p.character ^ 2 = 1 ∧ r.character = p.character ∧
        s.character = p.character) := by
  obtain ⟨p, r, s, hpr, hcpr, hps, hcps, hrs, hcrs⟩ := general_product_five_extract_three hcount
  refine ⟨p, r, s, ⟨hpr, hcpr, hps, hcps, hrs, hcrs⟩, ?_, ?_⟩
  · by_contra! hn
    exact t1_ordinary_pair_regular_impossible hx hq p r s hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  · rintro ⟨hc, hsq, hcr, hcs⟩
    exact t1_ordinary_quadratic_three_impossible hx hq p r s hpr hps hrs hcpr hcps hcrs hcr hcs hc hsq

end LiuWang.Proof.MultiZeroRepulsion.Continuation
