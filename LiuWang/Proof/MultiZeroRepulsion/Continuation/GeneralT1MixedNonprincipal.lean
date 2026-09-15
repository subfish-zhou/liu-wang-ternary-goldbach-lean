import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1RepeatedPair

/-! Actual four-sign three-slot exclusion when a third nonprincipal label is separated from the other two. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1SourceG_pair_regular_single_bound {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) (ha : 9 / 10 ≤ alpha)
    (p r s : ZeroSlots q alpha (x / q)) (hp : p.character ≠ 1)
    (hr : r.character ≠ 1) (hsc : s.character ≠ 1)
    (hpr : p.character * r.character ≠ 1) (hps : p.character * s.character ≠ 1)
    (hrs : r.character * s.character ≠ 1)
    (hgr : 1 - r.value.re ≤ sigma - 1) (hgs : 1 - s.value.re ≤ sigma - 1) :
    t1SourceG p.character r.character s.character sigma p.value.im r.value.im s.value.im +
      1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) + 1 / (sigma - s.value.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 12 / 5 := by
  have hh := t1SourceG_pair_regular_bound hq hs hs1 ha p r s hp hr hsc hpr hps hrs hgr hgs
  have hm (z : ZeroSlots q alpha (x / q)) :
      1 / (sigma - z.value.re) ≤
        (analyticOrderNatAt z.character.LFunction z.value : ℝ) / (sigma - z.value.re) := by
    have h1 : (1 : ℝ) ≤ analyticOrderNatAt z.character.LFunction z.value := by
      exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) z.index_lt)
    exact div_le_div_of_nonneg_right h1
      (by linarith [(mem_strictZeroValues.mp z.zero_mem).2.2.2.1])
  linarith [hm p, hm r, hm s]

theorem t1_ordinary_separated_third_impossible {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q))
    (hp : p.character ≠ 1) (hr : r.character ≠ 1) (hs : s.character ≠ 1)
    (hpr : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hcross : ∀ b c : Bool,
      p.character * t1Orient s.character c ≠ 1 ∧
      t1Orient r.character b * t1Orient s.character c ≠ 1) : False := by
  have hsig := t1Sigma_parameters hx
  have hsmall := t1_source_pole_domain hx
  have hgap (z : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q)) :
      1 - z.value.re ≤ t1Sigma x - 1 := by
    linarith [hsig.2.2.2, (mem_strictZeroValues.mp z.zero_mem).2.2.1]
  have hG (b c : Bool) :
      t1SourceG p.character (t1OrientSlot r b).character (t1OrientSlot s c).character (t1Sigma x)
        p.value.im (t1OrientSlot r b).value.im (t1OrientSlot s c).value.im +
        1 / (t1Sigma x - p.value.re) + 1 / (t1Sigma x - (t1OrientSlot r b).value.re) +
        1 / (t1Sigma x - (t1OrientSlot s c).value.re) ≤
        1 / (t1Sigma x - 1) + 7 * stechkinConductorCoeff * Real.log x + 12 / 5 := by
    have hr' : (t1OrientSlot r b).character ≠ 1 := by
      rw [t1OrientSlot_character]
      exact t1Orient_ne_one hr b
    have hs' : (t1OrientSlot s c).character ≠ 1 := by
      rw [t1OrientSlot_character]
      exact t1Orient_ne_one hs c
    have hps' : p.character * (t1OrientSlot s c).character ≠ 1 := by
      rw [t1OrientSlot_character]
      exact (hcross b c).1
    have hrs' : (t1OrientSlot r b).character * (t1OrientSlot s c).character ≠ 1 := by
      rw [t1OrientSlot_character, t1OrientSlot_character]
      exact (hcross b c).2
    by_cases hpair : p.character * (t1OrientSlot r b).character = 1
    · apply t1SourceG_repeated_pair_bound hq hsig.1 hsmall.1 hsmall.2 p (t1OrientSlot r b)
        (t1OrientSlot s c) hp hr' hs' hpair hps' hrs' _ (hgap p) (hgap _)
      cases b <;> simp only [t1OrientSlot, Bool.false_eq_true, if_false, if_true]
      · exact hnc
      · rw [conjugateSlot_involutive r]
        exact hpr
    · exact t1SourceG_pair_regular_single_bound hq hsig.1 hsmall.1 hsmall.2 p (t1OrientSlot r b)
        (t1OrientSlot s c) hp hr' hs' hpair hps' hrs' (hgap _) (hgap _)
  have h00 := hG false false
  have h10 := hG true false
  have h01 := hG false true
  have h11 := hG true true
  simp only [t1OrientSlot, Bool.false_eq_true, if_false, if_true] at h00 h10 h01 h11
  simp only [conjugateSlot_value, conj_re] at h10 h01 h11
  have he := t1SourceG_four_nonneg p r s hsig.1
  simp only [conjugateSlot_value] at he
  have zp := mem_strictZeroValues.mp p.zero_mem
  have zr := mem_strictZeroValues.mp r.zero_mem
  have zs := mem_strictZeroValues.mp s.zero_mem
  have hstrict := t1_scalar_twelve_fifths hx zp.2.2.1 zp.2.2.2.1 zr.2.2.1 zr.2.2.2.1 zs.2.2.1 zs.2.2.2.1
  linarith only [h00, h10, h01, h11, he, hstrict]

def t1SameLabelOrbit {q : ℕ} (chi psi : DirichletCharacter ℂ q) : Prop :=
  chi = psi ∨ chi = psi⁻¹

theorem t1SameLabelOrbit_symm {q : ℕ} {chi psi : DirichletCharacter ℂ q}
    (h : t1SameLabelOrbit chi psi) : t1SameLabelOrbit psi chi := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, inv_inv])

theorem t1SameLabelOrbit_trans {q : ℕ} {chi psi eta : DirichletCharacter ℂ q}
    (h : t1SameLabelOrbit chi psi) (h' : t1SameLabelOrbit psi eta) : t1SameLabelOrbit chi eta := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl (h.trans h')
  · exact Or.inr (h.trans h')
  · exact Or.inr (by rw [h, h'])
  · exact Or.inl (by rw [h, h', inv_inv])

theorem t1_oriented_product_ne {q : ℕ} {chi psi : DirichletCharacter ℂ q}
    (h : ¬ t1SameLabelOrbit chi psi) (b c : Bool) :
    t1Orient chi b * t1Orient psi c ≠ 1 := by
  intro hp
  have hh := mul_eq_one_iff_eq_inv.mp hp
  apply h
  cases b <;> cases c <;> simp only [t1Orient, Bool.false_eq_true, if_false, if_true, inv_inv] at hh
  · exact Or.inr hh
  · exact Or.inl hh
  · exact Or.inl (inv_injective hh)
  · exact Or.inr (by rw [← hh, inv_inv])

theorem t1_ordinary_nonprincipal_three_same_orbit {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q))
    (hp : p.character ≠ 1) (hr : r.character ≠ 1) (hs : s.character ≠ 1)
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s)
    (hcpr : p ≠ conjugateSlot r) (hcps : p ≠ conjugateSlot s) (hcrs : r ≠ conjugateSlot s) :
    t1SameLabelOrbit p.character r.character ∧ t1SameLabelOrbit p.character s.character := by
  have hex (p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q))
      (hp : p.character ≠ 1) (hr : r.character ≠ 1) (hs : s.character ≠ 1)
      (hpr : p ≠ r) (hnc : p ≠ conjugateSlot r)
      (hps : ¬ t1SameLabelOrbit p.character s.character)
      (hrs : ¬ t1SameLabelOrbit r.character s.character) : False :=
    t1_ordinary_separated_third_impossible hx hq p r s hp hr hs hpr hnc
      (fun b c ↦ ⟨t1_oriented_product_ne hps false c, t1_oriented_product_ne hrs b c⟩)
  have h1 : t1SameLabelOrbit p.character r.character := by
    by_contra h
    by_cases h' : t1SameLabelOrbit p.character s.character
    · exact hex p s r hp hs hr hps hcps h
        (fun hh ↦ h (t1SameLabelOrbit_trans h' hh))
    · exact hex r s p hr hs hp hrs hcrs
        (fun hh ↦ h (t1SameLabelOrbit_symm hh))
        (fun hh ↦ h' (t1SameLabelOrbit_symm hh))
  refine ⟨h1, ?_⟩
  by_contra h
  exact hex p r s hp hr hs hpr hcpr h
    (fun hh ↦ h (t1SameLabelOrbit_trans h1 hh))

theorem t1_product_five_forces_principal_or_one_orbit {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hcount : 4 < ∑ rho ∈ productZeroValues q (1 - (26213 / 100000) / Real.log x) (x / q),
      analyticOrderNatAt (productL q) rho) :
    ∃ p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q),
      (p ≠ r ∧ p ≠ conjugateSlot r ∧ p ≠ s ∧ p ≠ conjugateSlot s ∧
        r ≠ s ∧ r ≠ conjugateSlot s) ∧
      (p.character = 1 ∨ r.character = 1 ∨ s.character = 1 ∨
        (t1SameLabelOrbit p.character r.character ∧ t1SameLabelOrbit p.character s.character)) ∧
      ¬(p.character ≠ 1 ∧ p.character ^ 2 = 1 ∧ r.character = p.character ∧ s.character = p.character) := by
  obtain ⟨p, r, s, hpr, hcpr, hps, hcps, hrs, hcrs⟩ := general_product_five_extract_three hcount
  refine ⟨p, r, s, ⟨hpr, hcpr, hps, hcps, hrs, hcrs⟩, ?_, ?_⟩
  · by_cases hp : p.character = 1
    · exact Or.inl hp
    by_cases hr : r.character = 1
    · exact Or.inr (Or.inl hr)
    by_cases hs : s.character = 1
    · exact Or.inr (Or.inr (Or.inl hs))
    exact Or.inr (Or.inr (Or.inr
      (t1_ordinary_nonprincipal_three_same_orbit hx hq p r s hp hr hs hpr hps hrs hcpr hcps hcrs)))
  · rintro ⟨hc, hsq, hcr, hcs⟩
    exact t1_ordinary_quadratic_three_impossible hx hq p r s hpr hps hrs hcpr hcps hcrs hcr hcs hc hsq

end LiuWang.Proof.MultiZeroRepulsion.Continuation
