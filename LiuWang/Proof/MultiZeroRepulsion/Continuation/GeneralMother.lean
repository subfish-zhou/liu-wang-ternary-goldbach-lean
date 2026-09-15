import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralCount

/-! Variable-width two-slot repulsion, including imprimitive repeated and inverse labels. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem general_same_label_mother {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hc : p.character = r.character)
    (hne : p ≠ r) (hnc : p ≠ conjugateSlot r) (hn : p.character ≠ 1)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  let chi := p.character
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hx0 : 0 ≤ x := by linarith
  let a := general_inducing_slot chi hn hx0 p rfl
  let b := general_inducing_slot chi hn hx0 r hc.symm
  have hdx : (chi.conductor : ℝ) ≤ x := (show (chi.conductor : ℝ) ≤ q by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level).trans hq
  have hp := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hn
  have hab : a ≠ b := by
    intro he
    have hv := congrArg ZeroSlots.value he
    have hi := congrArg ZeroSlots.index he
    exact hne (zeroSlots_ext hc hv hi)
  have hac : a ≠ conjugateSlot b := by
    intro he
    have hchar := congrArg ZeroSlots.character he
    rw [conjugateSlot_character] at hchar
    change chi.primitiveCharacter = chi.primitiveCharacter⁻¹ at hchar
    have hself : chi = chi⁻¹ := by
      have hh := congrArg (DirichletCharacter.changeLevel chi.conductor_dvd_level) hchar
      simpa only [map_inv, DirichletCharacter.changeLevel_primitiveCharacter] using hh
    have hv := congrArg ZeroSlots.value he
    have hi := congrArg ZeroSlots.index he
    rw [conjugateSlot_value] at hv
    rw [conjugateSlot_index] at hi
    apply hnc
    apply zeroSlots_ext
    · rw [conjugateSlot_character, ← hc]
      exact hself
    · rw [conjugateSlot_value]
      exact hv
    · rw [conjugateSlot_index]
      exact hi
  by_cases hsq : chi.primitiveCharacter ^ 2 = 1
  · exact quadratic_label_global hx hdx hs hs1 ha a b rfl hab hac hp
      chi.primitiveCharacter_isPrimitive hsq hgp hgr
  · exact repeated_label_global hx hdx hs hs1 ha a b rfl hab hp
      chi.primitiveCharacter_isPrimitive hsq hgp hgr

theorem general_nonprincipal_mother {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r : ZeroSlots q alpha (x / q)) (hne : p ≠ r) (hnc : p ≠ conjugateSlot r)
    (hp : p.character ≠ 1) (hr : r.character ≠ 1)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) ≤
      1 / (sigma - 1) + 3 * stechkinConductorCoeff * Real.log x := by
  by_cases he : p.character = r.character
  · exact general_same_label_mother hx hq hs hs1 ha p r he hne hnc hp hgp hgr
  by_cases hi : p.character = r.character⁻¹
  · have hne' : p ≠ conjugateSlot (conjugateSlot r) := by
      rwa [conjugateSlot_involutive]
    have hh := general_same_label_mother hx hq hs hs1 ha p (conjugateSlot r)
      (by rwa [conjugateSlot_character]) hnc hne' hp hgp
      (by simpa only [conjugateSlot_value, conj_re] using hgr)
    simpa only [conjugateSlot_value, conj_re] using hh
  · have hm : p.character * r.character ≠ 1 := fun h => hi (mul_eq_one_iff_eq_inv.mp h)
    have hzp := mem_strictZeroValues.mp p.zero_mem
    have hzr := mem_strictZeroValues.mp r.zero_mem
    have hh := general_distinct_pair_global hq p.character r.character hp hr hm he
      (ha.trans_lt hzp.2.2.1) hzp.2.2.2.1 (ha.trans_lt hzr.2.2.1) hzr.2.2.2.1
      hzp.2.2.2.2 hzr.2.2.2.2 hs hs1
    have hmp : (1 : ℝ) ≤ analyticOrderNatAt p.character.LFunction p.value := by
      exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) p.index_lt)
    have hmr : (1 : ℝ) ≤ analyticOrderNatAt r.character.LFunction r.value := by
      exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) r.index_lt)
    have h1 := div_le_div_of_nonneg_right hmp (show 0 ≤ sigma - p.value.re by linarith [hzp.2.2.2.1])
    have h2 := div_le_div_of_nonneg_right hmr (show 0 ≤ sigma - r.value.re by linarith [hzr.2.2.2.1])
    linarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
