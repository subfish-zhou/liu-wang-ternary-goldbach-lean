import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.SelectedCosts

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

structure CountedData {d e f : ℕ} [NeZero d] [NeZero e] [NeZero f]
    (x : ℝ) (q : ℕ) [NeZero q] (alpha : ℝ)
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (eta : DirichletCharacter ℂ f) (p r u : ZeroSlots q alpha (x / q)) : Prop where
  scale_ge : 8000000000 ≤ x
  level_le : (q : ℝ) ≤ x
  chi_dvd : d ∣ q
  psi_dvd : e ∣ q
  eta_dvd : f ∣ q
  chi_primitive : chi.IsPrimitive
  psi_primitive : psi.IsPrimitive
  eta_primitive : eta.IsPrimitive
  p_label : p.character = chi.changeLevel chi_dvd
  r_label : r.character = psi.changeLevel psi_dvd
  u_label : u.character = eta.changeLevel eta_dvd
  re_gt_half : 1 / 2 < p.value.re ∧ 1 / 2 < r.value.re ∧ 1 / 2 < u.value.re
  separation : p ≠ r ∧ p ≠ conjugateSlot r ∧ p ≠ u ∧ p ≠ conjugateSlot u ∧
    r ≠ u ∧ r ≠ conjugateSlot u
  gaps : 1 - p.value.re ≤ lwdSourceSigma x - 1 ∧
    1 - r.value.re ≤ lwdSourceSigma x - 1 ∧ 1 - u.value.re ≤ lwdSourceSigma x - 1

theorem canonical_counted_data {q : ℕ} [NeZero q] {alpha x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r u : ZeroSlots q alpha (x / q))
    (hr : 1 / 2 < p.value.re ∧ 1 / 2 < r.value.re ∧ 1 / 2 < u.value.re)
    (hg : 1 - p.value.re ≤ lwdSourceSigma x - 1 ∧
      1 - r.value.re ≤ lwdSourceSigma x - 1 ∧ 1 - u.value.re ≤ lwdSourceSigma x - 1)
    (hsep : p ≠ r ∧ p ≠ conjugateSlot r ∧ p ≠ u ∧ p ≠ conjugateSlot u ∧
      r ≠ u ∧ r ≠ conjugateSlot u) :
    CountedData x q alpha p.character.primitiveCharacter r.character.primitiveCharacter
      u.character.primitiveCharacter p r u where
  scale_ge := hx
  level_le := hq
  chi_dvd := p.character.conductor_dvd_level
  psi_dvd := r.character.conductor_dvd_level
  eta_dvd := u.character.conductor_dvd_level
  chi_primitive := p.character.primitiveCharacter_isPrimitive
  psi_primitive := r.character.primitiveCharacter_isPrimitive
  eta_primitive := u.character.primitiveCharacter_isPrimitive
  p_label := p.character.changeLevel_primitiveCharacter.symm
  r_label := r.character.changeLevel_primitiveCharacter.symm
  u_label := u.character.changeLevel_primitiveCharacter.symm
  re_gt_half := hr
  separation := hsep
  gaps := hg

theorem slot_conjugate_separation {q : ℕ} [NeZero q] {alpha y : ℝ}
    {p r : ZeroSlots q alpha y} (h : p ≠ conjugateSlot r) : r ≠ conjugateSlot p := by
  intro he
  apply h
  rw [he, conjugateSlot_involutive]

def signedSlot {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ZeroSlots q alpha y) (b : Bool) :
    ZeroSlots q alpha y := if b then conjugateSlot p else p

theorem signed_slot_separation {q : ℕ} [NeZero q] {alpha y : ℝ}
    {p r : ZeroSlots q alpha y} (hne : p ≠ r) (hnc : p ≠ conjugateSlot r) (a b : Bool) :
    signedSlot p a ≠ signedSlot r b ∧ signedSlot p a ≠ conjugateSlot (signedSlot r b) := by
  have hn' : conjugateSlot p ≠ r := (slot_conjugate_separation hnc).symm
  have hnc' : conjugateSlot p ≠ conjugateSlot r := fun he => hne (conjugateSlot_involutive.injective he)
  cases a <;> cases b <;>
    simp only [signedSlot, Bool.false_eq_true, if_false, if_true, conjugateSlot_involutive r] <;>
    exact ⟨by assumption, by assumption⟩

theorem counted_data_signed {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    {x alpha : ℝ} {chi : DirichletCharacter ℂ d} {psi : DirichletCharacter ℂ e}
    {eta : DirichletCharacter ℂ f} {p r u : ZeroSlots q alpha (x / q)}
    (h : CountedData x q alpha chi psi eta p r u) (a b c : Bool) :
    CountedData x q alpha (lwdSignedCharacter chi a) (lwdSignedCharacter psi b)
      (lwdSignedCharacter eta c) (signedSlot p a) (signedSlot r b) (signedSlot u c) where
  scale_ge := h.scale_ge
  level_le := h.level_le
  chi_dvd := h.chi_dvd
  psi_dvd := h.psi_dvd
  eta_dvd := h.eta_dvd
  chi_primitive := lwd_signed_primitive chi h.chi_primitive a
  psi_primitive := lwd_signed_primitive psi h.psi_primitive b
  eta_primitive := lwd_signed_primitive eta h.eta_primitive c
  p_label := by cases a <;> simp [signedSlot, lwdSignedCharacter, conjugateSlot_character, h.p_label]
  r_label := by cases b <;> simp [signedSlot, lwdSignedCharacter, conjugateSlot_character, h.r_label]
  u_label := by cases c <;> simp [signedSlot, lwdSignedCharacter, conjugateSlot_character, h.u_label]
  re_gt_half := by
    cases a <;> cases b <;> cases c <;>
      simpa only [signedSlot, Bool.false_eq_true, if_false, if_true, conjugateSlot_value, conj_re]
        using h.re_gt_half
  separation := by
    have h1 := signed_slot_separation h.separation.1 h.separation.2.1 a b
    have h2 := signed_slot_separation h.separation.2.2.1 h.separation.2.2.2.1 a c
    have h3 := signed_slot_separation h.separation.2.2.2.2.1 h.separation.2.2.2.2.2 b c
    exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩
  gaps := by
    cases a <;> cases b <;> cases c <;>
      simpa only [signedSlot, Bool.false_eq_true, if_false, if_true, conjugateSlot_value, conj_re]
        using h.gaps

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
