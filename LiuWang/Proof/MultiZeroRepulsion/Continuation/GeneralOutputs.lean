import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralTripleSelection

/-! Full-strip Table 1 outputs: zeros to the left of the half-line are paid directly. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def general_raise_slot {q : ℕ} [NeZero q] {alpha beta y : ℝ}
    (p : ZeroSlots q alpha y) (hb : beta < p.value.re) : ZeroSlots q beta y where
  character := p.character
  value := p.value
  index := p.index
  zero_mem := by
    have hz := mem_strictZeroValues.mp p.zero_mem
    exact mem_strictZeroValues.mpr ⟨hz.1, hz.2.1, hb, hz.2.2.2.1, hz.2.2.2.2⟩
  index_lt := p.index_lt

theorem generalTable_full_strip (row : GeneralTableRow) {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q 0 (x / q)) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hl1 : (1 - p.value.re) * Real.log x ≤ generalTableFirst row) :
    generalTableSecond row ≤ (1 - r.value.re) * Real.log x := by
  have hL := source_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  have hc := generalTable_certificate row
  have hfirst : generalTableFirst row ≤ 1 / 2 :=
    hc.2.2.2.1.trans (hc.2.2.2.2.1.trans hc.2.1)
  have hsecond : generalTableSecond row ≤ 1 / 2 := hc.2.2.2.2.1.trans hc.2.1
  have hp : 1 / 2 < p.value.re := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - p.value.re by linarith) hL0.le
    linarith
  by_cases hr : 1 / 2 < r.value.re
  · let a := general_raise_slot p hp
    let b := general_raise_slot r hr
    have hab : a ≠ b := by
      intro he
      have hchar := congrArg ZeroSlots.character he
      have hval := congrArg ZeroSlots.value he
      have hindex := congrArg ZeroSlots.index he
      exact hne (zeroSlots_ext hchar hval hindex)
    have hac : a ≠ conjugateSlot b := by
      intro he
      have hchar := congrArg ZeroSlots.character he
      have hval := congrArg ZeroSlots.value he
      have hindex := congrArg ZeroSlots.index he
      rw [conjugateSlot_character] at hchar
      rw [conjugateSlot_value] at hval
      rw [conjugateSlot_index] at hindex
      apply hnc
      apply zeroSlots_ext
      · rw [conjugateSlot_character]
        exact hchar
      · rw [conjugateSlot_value]
        exact hval
      · rw [conjugateSlot_index]
        exact hindex
    exact generalTable_family row hx hq a b hab hac hl1
  · have hm := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - r.value.re by linarith) hL0.le
    linarith

theorem general_exceptional_3221_full_strip {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q 0 (x / q)) (hne : p ≠ r)
    (hc : p.character⁻¹ = p.character) (hr : p.value.im = 0)
    (hl : (1 - p.value.re) * Real.log x ≤ 12 / 100) :
    (3221 / 10000 : ℝ) ≤ (1 - r.value.re) * Real.log x := by
  have hf := (conjugateSlot_fixed_iff p).mpr ⟨hc, hr⟩
  have hnc : p ≠ conjugateSlot r := by
    intro he
    have hh := congrArg conjugateSlot he
    rw [hf, conjugateSlot_involutive] at hh
    exact hne hh
  exact generalTable_full_strip .r12 hx hq p r hne hnc hl

end LiuWang.Proof.MultiZeroRepulsion.Continuation
