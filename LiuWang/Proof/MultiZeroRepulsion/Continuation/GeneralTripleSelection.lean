import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralFamily

/-! The source's three nonconjugate objects extracted from the actual product multiplicity count. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_slot_outside {q : ℕ} [NeZero q] {alpha y : ℝ}
    (s : Finset (ZeroSlots q alpha y)) (h : s.card < strictFamilyCount q alpha y) :
    ∃ p : ZeroSlots q alpha y, p ∉ s := by
  by_contra! hn
  have hh := Finset.card_le_card
    (show (Finset.univ : Finset (ZeroSlots q alpha y)) ⊆ s from fun p _ => hn p)
  rw [Finset.card_univ, card_zeroSlots] at hh
  omega

theorem general_five_slots_extract_three {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hcount : 4 < strictFamilyCount q alpha y) :
    ∃ p r s : ZeroSlots q alpha y,
      p ≠ r ∧ p ≠ conjugateSlot r ∧
      p ≠ s ∧ p ≠ conjugateSlot s ∧
      r ≠ s ∧ r ≠ conjugateSlot s := by
  obtain ⟨p, _⟩ := general_slot_outside (q := q) (alpha := alpha) (y := y) ∅ (by simpa using
    (show 0 < strictFamilyCount q alpha y by omega))
  obtain ⟨r, hr⟩ := general_slot_outside ({p, conjugateSlot p} : Finset _)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨s, hs⟩ := general_slot_outside ({p, conjugateSlot p, r, conjugateSlot r} : Finset _)
    (lt_of_le_of_lt Finset.card_le_four hcount)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr hs
  have hc {a b : ZeroSlots q alpha y} (h : b ≠ conjugateSlot a) : a ≠ conjugateSlot b := by
    intro he
    have hh := congrArg conjugateSlot he
    rw [conjugateSlot_involutive] at hh
    exact h hh.symm
  exact ⟨p, r, s, Ne.symm hr.1, hc hr.2, Ne.symm hs.1, hc hs.2.1,
    Ne.symm hs.2.2.1, hc hs.2.2.2⟩

theorem general_product_five_extract_three {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hcount : 4 < ∑ rho ∈ productZeroValues q alpha y, analyticOrderNatAt (productL q) rho) :
    ∃ p r s : ZeroSlots q alpha y,
      p ≠ r ∧ p ≠ conjugateSlot r ∧
      p ≠ s ∧ p ≠ conjugateSlot s ∧
      r ≠ s ∧ r ≠ conjugateSlot s := by
  rw [← strictFamilyCount_eq_product_count] at hcount
  exact general_five_slots_extract_three hcount

end LiuWang.Proof.MultiZeroRepulsion.Continuation
