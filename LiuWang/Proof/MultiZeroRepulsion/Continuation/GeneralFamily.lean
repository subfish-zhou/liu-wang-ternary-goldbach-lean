import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralMixed
import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralTable

/-! The ordinary full-family two-point mother, Theorem 2 and Table 1. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_family_mother {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  by_cases hp : p.character = 1
  · by_cases hr : r.character = 1
    · exact general_principal_mother hx hs hs1 ha p r hp hr hne hnc hgp hgr
    · exact general_mixed_mother hx hq hs hs1 ha p r hp hr
  · by_cases hr : r.character = 1
    · simpa only [add_comm] using general_mixed_mother hx hq hs hs1 ha r p hr hp
    · exact general_nonprincipal_mother hx hq hs hs1 ha p r hne hnc hp hr hgp hgr

theorem general_family_slots_same_or_conjugate {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q)) :
    p = r ∨ p = conjugateSlot r := by
  by_contra hn
  have hne : p ≠ r := fun h => hn (Or.inl h)
  have hnc : p ≠ conjugateSlot r := fun h => hn (Or.inr h)
  obtain ⟨hs, hs1, ha, hgap⟩ := sourceSigma_parameters hx
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hm := general_family_mother hx hq hs hs1 ha p r hne hnc
    (by linarith [hp.2.2.1]) (by linarith [hr.2.2.1])
  exact (not_lt_of_ge hm) (source_reciprocal_sum_strict hx hp.2.2.1 hp.2.2.2.1 hr.2.2.1 hr.2.2.2.1)

theorem general_family_slots_card_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    Fintype.card (ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q)) ≤ 2 := by
  let α := ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q)
  by_cases h : Nonempty α
  · obtain ⟨p⟩ := h
    have hmem (r : α) : r ∈ ({p, conjugateSlot p} : Finset _) := by
      rcases general_family_slots_same_or_conjugate hx hq r p with he | he <;> simp [he]
    let f : α → {r // r ∈ ({p, conjugateSlot p} : Finset _)} := fun r => ⟨r, hmem r⟩
    have hf : Function.Injective f := by
      intro r s he
      exact congrArg Subtype.val he
    have hh := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_coe] at hh
    exact hh.trans Finset.card_le_two
  · have : IsEmpty α := not_nonempty_iff.mp h
    simpa only [show ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q) = α from rfl,
      Fintype.card_of_isEmpty] using (show (0 : ℕ) ≤ 2 by norm_num)

theorem general_theorem_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    strictFamilyCount q (1 - (2067 / 10000) / Real.log x) (x / q) ≤ 2 := by
  rw [← card_zeroSlots]
  exact general_family_slots_card_le_two hx hq

theorem general_product_theorem_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    (∑ rho ∈ productZeroValues q (1 - (2067 / 10000) / Real.log x) (x / q),
      analyticOrderNatAt (productL q) rho) ≤ 2 := by
  rw [← strictFamilyCount_eq_product_count]
  exact general_theorem_two hx hq

theorem generalTable_family (row : GeneralTableRow) {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 / 2) (x / q)) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hl1 : (1 - p.value.re) * Real.log x ≤ generalTableFirst row) :
    generalTableSecond row ≤ (1 - r.value.re) * Real.log x := by
  by_contra hn
  have hl2 := lt_of_not_ge hn
  have hL : 0 < Real.log x := by linarith [source_log_lower hx]
  have hc := generalTable_certificate row
  have hg1 : 1 - p.value.re ≤ (1 + generalTableA row / Real.log x) - 1 := by
    have hh : (1 - p.value.re) * Real.log x ≤ generalTableA row :=
      hl1.trans (hc.2.2.2.1.trans hc.2.2.2.2.1)
    have he := (le_div_iff₀ hL).mpr hh
    linarith
  have hg2 : 1 - r.value.re ≤ (1 + generalTableA row / Real.log x) - 1 := by
    have hh : (1 - r.value.re) * Real.log x ≤ generalTableA row := hl2.le.trans hc.2.2.2.2.1
    have he := (le_div_iff₀ hL).mpr hh
    linarith
  have hs := generalTable_parameters row hx
  have hm := general_family_mother hx hq hs.1 hs.2.1 le_rfl p r hne hnc hg1 hg2
  have hb := generalTable_scalar row hx (mem_strictZeroValues.mp p.zero_mem).2.2.2.1
    (mem_strictZeroValues.mp r.zero_mem).2.2.2.1 hl1 hl2
  exact (not_lt_of_ge hm) hb

theorem general_exceptional_3221 {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 / 2) (x / q)) (hne : p ≠ r)
    (hc : p.character⁻¹ = p.character) (hr : p.value.im = 0)
    (hl : (1 - p.value.re) * Real.log x ≤ 12 / 100) :
    (3221 / 10000 : ℝ) ≤ (1 - r.value.re) * Real.log x := by
  have hf := (conjugateSlot_fixed_iff p).mpr ⟨hc, hr⟩
  have hnc : p ≠ conjugateSlot r := by
    intro he
    have hh := congrArg conjugateSlot he
    rw [hf, conjugateSlot_involutive] at hh
    exact hne hh
  exact generalTable_family .r12 hx hq p r hne hnc hl

end LiuWang.Proof.MultiZeroRepulsion.Continuation
