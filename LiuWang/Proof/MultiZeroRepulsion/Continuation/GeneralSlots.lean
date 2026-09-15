import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralPair

/-! Multiplicity-preserving conductor transport for a repeated ordinary character label. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def general_inducing_slot {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) {x alpha : ℝ} (hx : 0 ≤ x)
    (p : ZeroSlots q alpha (x / q)) (hp : p.character = chi) :
    ZeroSlots chi.conductor alpha (x / chi.conductor) where
  character := chi.primitiveCharacter
  value := p.value
  index := p.index
  zero_mem := by
    have hz := mem_strictZeroValues.mp p.zero_mem
    rw [hp] at hz
    apply mem_strictZeroValues.mpr
    refine ⟨primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc hz.2.1 hz.1,
      hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.trans ?_⟩
    exact div_le_div_of_nonneg_left hx
      (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level)
  index_lt := by
    have hh := p.index_lt
    rw [hp, analyticOrderNatAt_LFunction_eq_primitive chi hc
      (mem_strictZeroValues.mp p.zero_mem).2.1] at hh
    exact hh

theorem general_inducing_slot_value {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) {x alpha : ℝ} (hx : 0 ≤ x)
    (p : ZeroSlots q alpha (x / q)) (hp : p.character = chi) :
    (general_inducing_slot chi hc hx p hp).value = p.value := rfl

theorem general_inducing_slot_index {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] (hc : chi ≠ 1) {x alpha : ℝ} (hx : 0 ≤ x)
    (p : ZeroSlots q alpha (x / q)) (hp : p.character = chi) :
    (general_inducing_slot chi hc hx p hp).index = p.index := rfl

theorem general_same_label_or_conjugate {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character = r.character) (hn : p.character ≠ 1) :
    p = r ∨ p = conjugateSlot r := by
  let chi := p.character
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hx0 : 0 ≤ x := by linarith
  let a := general_inducing_slot chi hn hx0 p rfl
  let b := general_inducing_slot chi hn hx0 r hc.symm
  have hdx : (chi.conductor : ℝ) ≤ x := (show (chi.conductor : ℝ) ≤ q by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level).trans hq
  have hp := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hn
  have hh := primitive_same_label_or_conjugate hx hdx a b rfl hp chi.primitiveCharacter_isPrimitive
  rcases hh with he | he
  · have hv := congrArg ZeroSlots.value he
    have hi := congrArg ZeroSlots.index he
    exact Or.inl (zeroSlots_ext hc hv hi)
  · have hchar := congrArg ZeroSlots.character he
    rw [conjugateSlot_character] at hchar
    change chi.primitiveCharacter = chi.primitiveCharacter⁻¹ at hchar
    have hself : chi = chi⁻¹ := by
      have h := congrArg (DirichletCharacter.changeLevel chi.conductor_dvd_level) hchar
      simpa only [map_inv, DirichletCharacter.changeLevel_primitiveCharacter] using h
    have hval := congrArg ZeroSlots.value he
    have hind := congrArg ZeroSlots.index he
    rw [conjugateSlot_value] at hval
    rw [conjugateSlot_index] at hind
    apply Or.inr
    apply zeroSlots_ext
    · rw [conjugateSlot_character, ← hc]
      exact hself
    · rw [conjugateSlot_value]
      exact hval
    · rw [conjugateSlot_index]
      exact hind

theorem general_nonprincipal_slots_same_or_conjugate {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character ≠ 1) (hd : r.character ≠ 1) :
    p = r ∨ p = conjugateSlot r := by
  rcases general_slots_labels hx hq p r hc hd with he | he
  · exact general_same_label_or_conjugate hx hq p r he hc
  · have hcc : p.character = (conjugateSlot r).character := by
      rw [conjugateSlot_character]
      exact he
    have hh := general_same_label_or_conjugate hx hq p (conjugateSlot r) hcc hc
    rw [conjugateSlot_involutive] at hh
    exact hh.symm

end LiuWang.Proof.MultiZeroRepulsion.Continuation
