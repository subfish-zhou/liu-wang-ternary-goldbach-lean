import LiuWang.Proof.MultiZeroRepulsion.Continuation.QuadraticPair

/-! The original two-zero region for the full primitive nonprincipal subfamily. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def sourceSigma (x : ℝ) : ℝ := 1 + (499 / 1000) / Real.log x

theorem sourceSigma_parameters {x : ℝ} (hx : 8000000000 ≤ x) :
    1 < sourceSigma x ∧ sourceSigma x ≤ 23 / 20 ∧
      1 / 2 ≤ 1 - (2067 / 10000) / Real.log x ∧
      (2067 / 10000) / Real.log x ≤ sourceSigma x - 1 := by
  have hL := source_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  have hd : 0 < (499 / 1000 : ℝ) / Real.log x := by positivity
  have hd1 : (499 / 1000 : ℝ) / Real.log x ≤ 3 / 20 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hw : (2067 / 10000 : ℝ) / Real.log x ≤ 1 / 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hgap : (2067 / 10000 : ℝ) / Real.log x ≤ (499 / 1000) / Real.log x :=
    div_le_div_of_nonneg_right (by norm_num) hL0.le
  dsimp [sourceSigma]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem source_reciprocal_sum_strict {x beta gamma : ℝ} (hx : 8000000000 ≤ x)
    (hb : 1 - (2067 / 10000) / Real.log x < beta) (hb1 : beta < 1)
    (hg : 1 - (2067 / 10000) / Real.log x < gamma) (hg1 : gamma < 1) :
    1 / (sourceSigma x - 1) + 3 * stechkinConductorCoeff * Real.log x <
      1 / (sourceSigma x - beta) + 1 / (sourceSigma x - gamma) := by
  have hL := source_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  have hs := (sourceSigma_parameters hx).1
  have hsL : (sourceSigma x - 1) * Real.log x = 499 / 1000 := by
    dsimp [sourceSigma]
    field_simp
    ring
  have hbr : (1 - beta) * Real.log x < 2067 / 10000 := by
    apply (lt_div_iff₀ hL0).mp
    linarith
  have hbt : (1 - gamma) * Real.log x < 2067 / 10000 := by
    apply (lt_div_iff₀ hL0).mp
    linarith
  have hlowp : Real.log x / (7057 / 10000) < 1 / (sourceSigma x - beta) := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).mpr
    nlinarith
  have hlowr : Real.log x / (7057 / 10000) < 1 / (sourceSigma x - gamma) := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).mpr
    nlinarith
  have hinv : 1 / (sourceSigma x - 1) = Real.log x / (499 / 1000) := by
    dsimp [sourceSigma]
    field_simp
    ring
  rw [hinv]
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  norm_num [div_eq_mul_inv] at hlowp hlowr hk ⊢
  nlinarith only [hlowp, hlowr, hk, hL0]

theorem primitive_same_label_or_conjugate {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character = r.character) (hnp : p.character ≠ 1)
    (hprim : p.character.IsPrimitive) : p = r ∨ p = conjugateSlot r := by
  by_cases hsq : p.character ^ 2 = 1
  · by_contra hn
    have hne : p ≠ r := fun he => hn (Or.inl he)
    have hnc : p ≠ conjugateSlot r := fun he => hn (Or.inr he)
    obtain ⟨hs, hs1, ha, hgap⟩ := sourceSigma_parameters hx
    have hp := mem_strictZeroValues.mp p.zero_mem
    have hr := mem_strictZeroValues.mp r.zero_mem
    have hh := quadratic_label_global hx hq hs hs1 ha p r hc hne hnc hnp hprim hsq
      (by linarith [hp.2.2.1]) (by linarith [hr.2.2.1])
    exact (not_lt_of_ge hh) (source_reciprocal_sum_strict hx hp.2.2.1 hp.2.2.2.1 hr.2.2.1 hr.2.2.2.1)
  · exact Or.inl (repeated_label_unique hx hq p r hc hprim hsq)

theorem primitive_slots_same_or_conjugate {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character ≠ 1) (hp : p.character.IsPrimitive)
    (hd : r.character ≠ 1) (hr : r.character.IsPrimitive) :
    p = r ∨ p = conjugateSlot r := by
  rcases primitive_slots_same_or_inverse hx hq p r hc hp hd hr with he | he
  · exact primitive_same_label_or_conjugate hx hq p r he hc hp
  · have hcc : p.character = (conjugateSlot r).character := by
      rw [conjugateSlot_character]
      exact he
    have hh := primitive_same_label_or_conjugate hx hq p (conjugateSlot r) hcc hc hp
    rw [conjugateSlot_involutive] at hh
    exact hh.symm

def PrimitiveNonprincipalSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  {p : ZeroSlots q alpha y // p.character.IsPrimitive ∧ p.character ≠ 1}

instance primitiveNonprincipalSlotsFintype (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype (PrimitiveNonprincipalSlots q alpha y) :=
  inferInstanceAs (Fintype {p : ZeroSlots q alpha y // p.character.IsPrimitive ∧ p.character ≠ 1})

theorem primitive_nonprincipal_slots_card_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    Fintype.card (PrimitiveNonprincipalSlots q (1 - (2067 / 10000) / Real.log x) (x / q)) ≤ 2 := by
  let α := PrimitiveNonprincipalSlots q (1 - (2067 / 10000) / Real.log x) (x / q)
  by_cases h : Nonempty α
  · obtain ⟨p⟩ := h
    have hmem (r : α) : r.val ∈ ({p.val, conjugateSlot p.val} : Finset _) := by
      rcases primitive_slots_same_or_conjugate hx hq r.val p.val
        r.property.2 r.property.1 p.property.2 p.property.1 with he | he <;> simp [he]
    let f : α → {r // r ∈ ({p.val, conjugateSlot p.val} : Finset _)} := fun r => ⟨r.val, hmem r⟩
    have hf : Function.Injective f := by
      intro r s he
      apply Subtype.ext
      exact congrArg (fun z : {r // r ∈ ({p.val, conjugateSlot p.val} : Finset _)} => z.val) he
    have hh := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_coe] at hh
    exact hh.trans Finset.card_le_two
  · have : IsEmpty α := not_nonempty_iff.mp h
    simpa only [show PrimitiveNonprincipalSlots q (1 - (2067 / 10000) / Real.log x) (x / q) = α from rfl,
      Fintype.card_of_isEmpty] using (show (0 : ℕ) ≤ 2 by norm_num)

def primitiveNonprincipalCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi : {chi : DirichletCharacter ℂ q // chi.IsPrimitive ∧ chi ≠ 1},
    ∑ rho ∈ strictZeroValues chi.val alpha y, analyticOrderNatAt chi.val.LFunction rho

def primitiveSlotsSigmaEquiv (q : ℕ) [NeZero q] (alpha y : ℝ) :
    PrimitiveNonprincipalSlots q alpha y ≃
      Σ chi : {chi : DirichletCharacter ℂ q // chi.IsPrimitive ∧ chi ≠ 1},
        Σ rho : {rho : ℂ // rho ∈ strictZeroValues chi.val alpha y},
          Fin (analyticOrderNatAt chi.val.LFunction rho.val) where
  toFun p := ⟨⟨p.val.character, p.property⟩,
    ⟨⟨p.val.value, p.val.zero_mem⟩, ⟨p.val.index, p.val.index_lt⟩⟩⟩
  invFun p := ⟨⟨p.1.val, p.2.1.val, p.2.2.val, p.2.1.property, p.2.2.isLt⟩, p.1.property⟩
  left_inv p := by rcases p with ⟨⟨chi, rho, k, hr, hk⟩, hc⟩; rfl
  right_inv p := by rcases p with ⟨⟨chi, hc⟩, ⟨⟨rho, hr⟩, ⟨k, hk⟩⟩⟩; rfl

theorem primitiveNonprincipalCount_eq_card (q : ℕ) [NeZero q] (alpha y : ℝ) :
    primitiveNonprincipalCount q alpha y = Fintype.card (PrimitiveNonprincipalSlots q alpha y) := by
  rw [Fintype.card_congr (primitiveSlotsSigmaEquiv q alpha y)]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_coe_sort, primitiveNonprincipalCount]

theorem primitiveNonprincipalCount_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    primitiveNonprincipalCount q (1 - (2067 / 10000) / Real.log x) (x / q) ≤ 2 := by
  rw [primitiveNonprincipalCount_eq_card]
  exact primitive_nonprincipal_slots_card_le_two hx hq

end LiuWang.Proof.MultiZeroRepulsion.Continuation
