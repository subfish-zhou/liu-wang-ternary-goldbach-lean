import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralSlots

/-! The full ordinary nonprincipal family at the original fixed modulus and closed height. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def GeneralNonprincipalSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  {p : ZeroSlots q alpha y // p.character ≠ 1}

instance generalNonprincipalSlotsFintype (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype (GeneralNonprincipalSlots q alpha y) :=
  inferInstanceAs (Fintype {p : ZeroSlots q alpha y // p.character ≠ 1})

theorem general_nonprincipal_slots_card_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    Fintype.card (GeneralNonprincipalSlots q (1 - (2067 / 10000) / Real.log x) (x / q)) ≤ 2 := by
  let α := GeneralNonprincipalSlots q (1 - (2067 / 10000) / Real.log x) (x / q)
  by_cases h : Nonempty α
  · obtain ⟨p⟩ := h
    have hmem (r : α) : r.val ∈ ({p.val, conjugateSlot p.val} : Finset _) := by
      rcases general_nonprincipal_slots_same_or_conjugate hx hq r.val p.val
        r.property p.property with he | he <;> simp [he]
    let f : α → {r // r ∈ ({p.val, conjugateSlot p.val} : Finset _)} := fun r => ⟨r.val, hmem r⟩
    have hf : Function.Injective f := by
      intro r s he
      apply Subtype.ext
      exact congrArg (fun z : {r // r ∈ ({p.val, conjugateSlot p.val} : Finset _)} => z.val) he
    have hh := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_coe] at hh
    exact hh.trans Finset.card_le_two
  · have : IsEmpty α := not_nonempty_iff.mp h
    simpa only [show GeneralNonprincipalSlots q (1 - (2067 / 10000) / Real.log x) (x / q) = α from rfl,
      Fintype.card_of_isEmpty] using (show (0 : ℕ) ≤ 2 by norm_num)

def generalNonprincipalCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi : {chi : DirichletCharacter ℂ q // chi ≠ 1},
    ∑ rho ∈ strictZeroValues chi.val alpha y, analyticOrderNatAt chi.val.LFunction rho

def generalSlotsSigmaEquiv (q : ℕ) [NeZero q] (alpha y : ℝ) :
    GeneralNonprincipalSlots q alpha y ≃
      Σ chi : {chi : DirichletCharacter ℂ q // chi ≠ 1},
        Σ rho : {rho : ℂ // rho ∈ strictZeroValues chi.val alpha y},
          Fin (analyticOrderNatAt chi.val.LFunction rho.val) where
  toFun p := ⟨⟨p.val.character, p.property⟩,
    ⟨⟨p.val.value, p.val.zero_mem⟩, ⟨p.val.index, p.val.index_lt⟩⟩⟩
  invFun p := ⟨⟨p.1.val, p.2.1.val, p.2.2.val, p.2.1.property, p.2.2.isLt⟩, p.1.property⟩
  left_inv p := by rcases p with ⟨⟨chi, rho, k, hr, hk⟩, hc⟩; rfl
  right_inv p := by rcases p with ⟨⟨chi, hc⟩, ⟨⟨rho, hr⟩, ⟨k, hk⟩⟩⟩; rfl

theorem generalNonprincipalCount_eq_card (q : ℕ) [NeZero q] (alpha y : ℝ) :
    generalNonprincipalCount q alpha y = Fintype.card (GeneralNonprincipalSlots q alpha y) := by
  rw [Fintype.card_congr (generalSlotsSigmaEquiv q alpha y)]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_coe_sort, generalNonprincipalCount]

theorem generalNonprincipalCount_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    generalNonprincipalCount q (1 - (2067 / 10000) / Real.log x) (x / q) ≤ 2 := by
  rw [generalNonprincipalCount_eq_card]
  exact general_nonprincipal_slots_card_le_two hx hq

end LiuWang.Proof.MultiZeroRepulsion.Continuation
