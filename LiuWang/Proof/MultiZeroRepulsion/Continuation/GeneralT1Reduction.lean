import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Quadratic

/-! Genuine ordinary triple consumers and the exact remaining alternatives after five-slot extraction. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_inducing_injective {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) {x alpha : ℝ} (hx : 0 ≤ x)
    (p r : ZeroSlots q alpha (x / q)) (hp : p.character = chi) (hr : r.character = chi)
    (hne : p ≠ r) :
    general_inducing_slot chi hc hx p hp ≠ general_inducing_slot chi hc hx r hr := by
  intro he
  have hv := congrArg ZeroSlots.value he
  have hi := congrArg ZeroSlots.index he
  exact hne (zeroSlots_ext (hp.trans hr.symm) hv hi)

theorem t1_inducing_nonconjugate {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) {x alpha : ℝ} (hx : 0 ≤ x)
    (p r : ZeroSlots q alpha (x / q)) (hp : p.character = chi) (hr : r.character = chi)
    (hne : p ≠ conjugateSlot r) :
    general_inducing_slot chi hc hx p hp ≠ conjugateSlot (general_inducing_slot chi hc hx r hr) := by
  intro he
  have hh := congrArg ZeroSlots.character he
  rw [conjugateSlot_character] at hh
  change chi.primitiveCharacter = chi.primitiveCharacter⁻¹ at hh
  have hself : chi = chi⁻¹ := by
    have h := congrArg (DirichletCharacter.changeLevel chi.conductor_dvd_level) hh
    simpa only [map_inv, DirichletCharacter.changeLevel_primitiveCharacter] using h
  have hv := congrArg ZeroSlots.value he
  have hi := congrArg ZeroSlots.index he
  rw [conjugateSlot_value] at hv
  rw [conjugateSlot_index] at hi
  apply hne
  apply zeroSlots_ext
  · rw [conjugateSlot_character, hp, hr]
    exact hself
  · rw [conjugateSlot_value]
    exact hv
  · rw [conjugateSlot_index]
    exact hi

theorem t1_ordinary_quadratic_three_impossible {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q))
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s)
    (hcpr : p ≠ conjugateSlot r) (hcps : p ≠ conjugateSlot s) (hcrs : r ≠ conjugateSlot s)
    (hcr : r.character = p.character) (hcs : s.character = p.character)
    (hc : p.character ≠ 1) (hsq : p.character ^ 2 = 1) : False := by
  let chi := p.character
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hx0 : 0 ≤ x := by linarith
  let a := general_inducing_slot chi hc hx0 p rfl
  let b := general_inducing_slot chi hc hx0 r hcr
  let c := general_inducing_slot chi hc hx0 s hcs
  have hd : (chi.conductor : ℝ) ≤ x := (show (chi.conductor : ℝ) ≤ q by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level).trans hq
  have hprim := chi.primitiveCharacter_isPrimitive
  have hp := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hsq' : chi.primitiveCharacter ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
    rw [map_pow, map_one, DirichletCharacter.changeLevel_primitiveCharacter]
    exact hsq
  have hs := t1Sigma_parameters hx
  have hsp := t1_source_pole_domain hx
  have zp := mem_strictZeroValues.mp p.zero_mem
  have zr := mem_strictZeroValues.mp r.zero_mem
  have zs := mem_strictZeroValues.mp s.zero_mem
  have hm := t1_quadratic_three_mother hd hs.1 hsp.1 hsp.2 a b c
    (t1_inducing_injective chi hc hx0 p r rfl hcr hpr)
    (t1_inducing_injective chi hc hx0 p s rfl hcs hps)
    (t1_inducing_injective chi hc hx0 r s hcr hcs hrs)
    (t1_inducing_nonconjugate chi hc hx0 p r rfl hcr hcpr)
    (t1_inducing_nonconjugate chi hc hx0 p s rfl hcs hcps)
    (t1_inducing_nonconjugate chi hc hx0 r s hcr hcs hcrs)
    rfl rfl hp hprim hsq'
    (by change 1 - p.value.re ≤ t1Sigma x - 1; linarith [hs.2.2.2, zp.2.2.1])
    (by change 1 - r.value.re ≤ t1Sigma x - 1; linarith [hs.2.2.2, zr.2.2.1])
    (by change 1 - s.value.re ≤ t1Sigma x - 1; linarith [hs.2.2.2, zs.2.2.1])
  exact (not_lt_of_ge hm) (t1_scalar_strict hx zp.2.2.1 zp.2.2.2.1 zr.2.2.1 zr.2.2.2.1 zs.2.2.1 zs.2.2.2.1)

theorem t1_product_five_forces_remaining_case {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hcount : 4 < ∑ rho ∈ productZeroValues q (1 - (26213 / 100000) / Real.log x) (x / q),
      analyticOrderNatAt (productL q) rho) :
    ∃ p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q),
      (p ≠ r ∧ p ≠ conjugateSlot r ∧ p ≠ s ∧ p ≠ conjugateSlot s ∧
        r ≠ s ∧ r ≠ conjugateSlot s) ∧
      (p.character = 1 ∨ r.character = 1 ∨ s.character = 1 ∨
        ∃ b c : Bool, p.character * t1Orient r.character b = 1 ∨
          p.character * t1Orient s.character c = 1 ∨
          t1Orient r.character b * t1Orient s.character c = 1 ∨
          p.character * t1Orient r.character b * t1Orient s.character c = 1) ∧
      ¬(p.character ≠ 1 ∧ p.character ^ 2 = 1 ∧ r.character = p.character ∧
        s.character = p.character) := by
  obtain ⟨p, r, s, hpr, hcpr, hps, hcps, hrs, hcrs⟩ := general_product_five_extract_three hcount
  refine ⟨p, r, s, ⟨hpr, hcpr, hps, hcps, hrs, hcrs⟩, ?_, ?_⟩
  · by_contra! hn
    have hp := hn.1
    have hr := hn.2.1
    have hs := hn.2.2.1
    have hproducts := hn.2.2.2
    exact t1_ordinary_nondegenerate_impossible hx hq p r s hp hr hs hproducts
  · rintro ⟨hc, hsq, hcr, hcs⟩
    exact t1_ordinary_quadratic_three_impossible hx hq p r s hpr hps hrs hcpr hcps hcrs hcr hcs hc hsq

end LiuWang.Proof.MultiZeroRepulsion.Continuation
