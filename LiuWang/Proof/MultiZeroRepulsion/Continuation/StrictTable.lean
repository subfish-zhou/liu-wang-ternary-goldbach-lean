import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralOutputs

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation.ParentStrictTable

theorem scalar_closed (r : GeneralTableRow) {x beta gamma : ℝ} (hx : 8000000000 ≤ x)
    (hb : beta < 1) (hg : gamma < 1)
    (hl1 : (1 - beta) * Real.log x ≤ generalTableFirst r)
    (hl2 : (1 - gamma) * Real.log x ≤ generalTableSecond r) :
    let sigma := 1 + generalTableA r / Real.log x
    1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x <
      1 / (sigma - beta) + 1 / (sigma - gamma) := by
  dsimp only
  have h := generalTable_certificate r
  have hL : 0 < Real.log x := by linarith [source_log_lower hx]
  have hs := (generalTable_parameters r hx).1
  have hp : 0 < generalTableA r + generalTableFirst r := by linarith [h.1, h.2.2.1]
  have hr : 0 < generalTableA r + generalTableSecond r := by
    linarith [h.1, h.2.2.1, h.2.2.2.1]
  have he : (1 + generalTableA r / Real.log x - 1) * Real.log x = generalTableA r := by
    field_simp
    ring
  have he' : 1 / (1 + generalTableA r / Real.log x - 1) = Real.log x / generalTableA r := by
    field_simp
    ring
  have hlp : Real.log x / (generalTableA r + generalTableFirst r) ≤
      1 / (1 + generalTableA r / Real.log x - beta) := by
    apply (div_le_div_iff₀ hp (by linarith)).mpr
    nlinarith
  have hlr : Real.log x / (generalTableA r + generalTableSecond r) ≤
      1 / (1 + generalTableA r / Real.log x - gamma) := by
    apply (div_le_div_iff₀ hr (by linarith)).mpr
    nlinarith
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hh := mul_lt_mul_of_pos_right h.2.2.2.2.2 hL
  rw [he']
  simp only [div_eq_mul_inv] at hlp hlr hh ⊢
  nlinarith only [hlp, hlr, hk, hh]

theorem family_strict (row : GeneralTableRow) {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 / 2) (x / q)) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hl1 : (1 - p.value.re) * Real.log x ≤ generalTableFirst row) :
    generalTableSecond row < (1 - r.value.re) * Real.log x := by
  by_contra hn
  have hl2 := le_of_not_gt hn
  have hL : 0 < Real.log x := by linarith [source_log_lower hx]
  have hc := generalTable_certificate row
  have hg1 : 1 - p.value.re ≤ (1 + generalTableA row / Real.log x) - 1 := by
    have hh : (1 - p.value.re) * Real.log x ≤ generalTableA row :=
      hl1.trans (hc.2.2.2.1.trans hc.2.2.2.2.1)
    have he := (le_div_iff₀ hL).mpr hh
    linarith
  have hg2 : 1 - r.value.re ≤ (1 + generalTableA row / Real.log x) - 1 := by
    have hh : (1 - r.value.re) * Real.log x ≤ generalTableA row := hl2.trans hc.2.2.2.2.1
    have he := (le_div_iff₀ hL).mpr hh
    linarith
  have hs := generalTable_parameters row hx
  have hm := general_family_mother hx hq hs.1 hs.2.1 le_rfl p r hne hnc hg1 hg2
  have hb := scalar_closed row hx (mem_strictZeroValues.mp p.zero_mem).2.2.2.1
    (mem_strictZeroValues.mp r.zero_mem).2.2.2.1 hl1 hl2
  exact (not_lt_of_ge hm) hb

theorem full_strip_strict (row : GeneralTableRow) {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q 0 (x / q)) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hl1 : (1 - p.value.re) * Real.log x ≤ generalTableFirst row) :
    generalTableSecond row < (1 - r.value.re) * Real.log x := by
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
    exact family_strict row hx hq a b hab hac hl1
  · have hm := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - r.value.re by linarith) hL0.le
    linarith

theorem exceptional_strict {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q 0 (x / q)) (hne : p ≠ r)
    (hc : p.character⁻¹ = p.character) (hr : p.value.im = 0)
    (hl : (1 - p.value.re) * Real.log x ≤ 12 / 100) :
    (3221 / 10000 : ℝ) < (1 - r.value.re) * Real.log x := by
  have hf := (conjugateSlot_fixed_iff p).mpr ⟨hc, hr⟩
  have hnc : p ≠ conjugateSlot r := by
    intro he
    have hh := congrArg conjugateSlot he
    rw [hf, conjugateSlot_involutive] at hh
    exact hne hh
  exact full_strip_strict .r12 hx hq p r hne hnc hl

end LiuWang.Proof.MultiZeroRepulsion.Continuation.ParentStrictTable
