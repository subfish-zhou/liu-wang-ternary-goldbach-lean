import LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples.Data

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.MultiZeroRepulsion LiuWang.Proof.MultiZeroRepulsion.Continuation
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples

def closedConjugate {q : ℕ} [NeZero q] {alpha y : ℝ} (p : ClosedSlots q alpha y) :
    ClosedSlots q alpha y := ⟨conjugateSlot p.val, p.property⟩

theorem closedConjugate_involutive {q : ℕ} [NeZero q] {alpha y : ℝ} :
    Function.Involutive (@closedConjugate q _ alpha y) := by
  intro p
  apply Subtype.ext
  exact conjugateSlot_involutive p.val

theorem closed_slot_outside {q : ℕ} [NeZero q] {alpha y : ℝ}
    (s : Finset (ClosedSlots q alpha y)) (h : s.card < familyCount q alpha y) :
    ∃ p : ClosedSlots q alpha y, p ∉ s := by
  by_contra! hn
  have hh := Finset.card_le_card
    (show (Finset.univ : Finset (ClosedSlots q alpha y)) ⊆ s from fun p _ => hn p)
  rw [Finset.card_univ, closedSlots_card] at hh
  omega

theorem closed_five_extract_three {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hcount : 4 < familyCount q alpha y) :
    ∃ p r u : ClosedSlots q alpha y,
      p.val ≠ r.val ∧ p.val ≠ conjugateSlot r.val ∧
      p.val ≠ u.val ∧ p.val ≠ conjugateSlot u.val ∧
      r.val ≠ u.val ∧ r.val ≠ conjugateSlot u.val := by
  obtain ⟨p, _⟩ := closed_slot_outside (q := q) (alpha := alpha) (y := y) ∅
    (by simpa using (show 0 < familyCount q alpha y by omega))
  obtain ⟨r, hr⟩ := closed_slot_outside ({p, closedConjugate p} : Finset _)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨u, hu⟩ := closed_slot_outside ({p, closedConjugate p, r, closedConjugate r} : Finset _)
    (lt_of_le_of_lt Finset.card_le_four hcount)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr hu
  have hpr : p.val ≠ r.val := fun he => hr.1 (Subtype.ext he.symm)
  have hpc : r.val ≠ conjugateSlot p.val := fun he => hr.2 (Subtype.ext he)
  have hpu : p.val ≠ u.val := fun he => hu.1 (Subtype.ext he.symm)
  have hpuc : u.val ≠ conjugateSlot p.val := fun he => hu.2.1 (Subtype.ext he)
  have hru : r.val ≠ u.val := fun he => hu.2.2.1 (Subtype.ext he.symm)
  have hruc : u.val ≠ conjugateSlot r.val := fun he => hu.2.2.2 (Subtype.ext he)
  exact ⟨p, r, u, hpr, slot_conjugate_separation hpc, hpu,
    slot_conjugate_separation hpuc, hru, slot_conjugate_separation hruc⟩

def closedProductValues (q : ℕ) [NeZero q] (alpha y : ℝ) : Finset ℂ :=
  (Finset.univ : Finset (DirichletCharacter ℂ q)).biUnion
    (fun chi => DirichletZeroCount.zeroValues chi alpha y)

theorem mem_closedProductValues {q : ℕ} [NeZero q] {alpha y : ℝ} {z : ℂ} :
    z ∈ closedProductValues q alpha y ↔
      productL q z = 0 ∧ 0 < z.re ∧ alpha ≤ z.re ∧ z.re < 1 ∧ |z.im| ≤ y := by
  simp only [closedProductValues, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_zeroValues, productL, Finset.prod_apply, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨chi, hz, ⟨h0, h1, hy⟩, ha⟩
    exact ⟨⟨chi, hz⟩, h0, ha, h1, hy⟩
  · rintro ⟨⟨chi, hz⟩, h0, ha, h1, hy⟩
    exact ⟨chi, hz, ⟨h0, h1, hy⟩, ha⟩

theorem closedFamilyCount_eq_product_count (q : ℕ) [NeZero q] (alpha y : ℝ) :
    familyCount q alpha y =
      ∑ z ∈ closedProductValues q alpha y, analyticOrderNatAt (productL q) z := by
  unfold familyCount count
  calc
    _ = ∑ chi : DirichletCharacter ℂ q, ∑ z ∈ closedProductValues q alpha y,
        analyticOrderNatAt chi.LFunction z := by
      apply Finset.sum_congr rfl
      intro chi _
      apply Finset.sum_subset
      · intro z hz
        exact Finset.mem_biUnion.mpr ⟨chi, Finset.mem_univ _, hz⟩
      · intro z hz hn
        by_contra ho
        have hh := mem_closedProductValues.mp hz
        exact hn (mem_zeroValues.mpr
          ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero ho, ⟨hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩, hh.2.2.1⟩)
    _ = ∑ z ∈ closedProductValues q alpha y, ∑ chi : DirichletCharacter ℂ q,
        analyticOrderNatAt chi.LFunction z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (productL_order q (by intro he; simpa [he] using
        (mem_closedProductValues.mp hz).2.2.2.1)).symm

theorem closed_card_eq_product_count (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype.card (ClosedSlots q alpha y) =
      ∑ z ∈ closedProductValues q alpha y, analyticOrderNatAt (productL q) z := by
  rw [closedSlots_card, closedFamilyCount_eq_product_count]

end LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart.OriginalV1.CountedTriples
