import LiuWang.Proof.MultiZeroRepulsion.Continuation.RepeatedLabel

/-! At most two actual multiplicity slots in the primitive nonquadratic subfamily. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem repeated_label_unique {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r : ZeroSlots q (1 - (2067 / 10000) / Real.log x) (x / q))
    (hc : p.character = r.character) (hprim : p.character.IsPrimitive)
    (hsq : p.character ^ 2 ≠ 1) : p = r := by
  by_contra hne
  have hnp : p.character ≠ 1 := by intro he; simp [he] at hsq
  have hp := mem_strictZeroValues.mp p.zero_mem
  have hr := mem_strictZeroValues.mp r.zero_mem
  have hL := source_log_lower hx
  have hL0 : 0 < Real.log x := by linarith
  let sigma := 1 + (499 / 1000) / Real.log x
  have hd : 0 < (499 / 1000 : ℝ) / Real.log x := by positivity
  have hd1 : (499 / 1000 : ℝ) / Real.log x ≤ 3 / 20 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hs : 1 < sigma := by dsimp [sigma]; linarith
  have hs1 : sigma ≤ 23 / 20 := by dsimp [sigma]; linarith
  have hw : (2067 / 10000 : ℝ) / Real.log x ≤ 1 / 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have ha : 1 / 2 ≤ 1 - (2067 / 10000) / Real.log x := by linarith
  have hgap : (2067 / 10000 : ℝ) / Real.log x ≤ (499 / 1000) / Real.log x :=
    div_le_div_of_nonneg_right (by norm_num) hL0.le
  have hgp : 1 - p.value.re ≤ sigma - 1 := by dsimp [sigma]; linarith [hp.2.2.1]
  have hgr : 1 - r.value.re ≤ sigma - 1 := by dsimp [sigma]; linarith [hr.2.2.1]
  have hmother := repeated_label_global hx hq hs hs1 ha p r hc hne hnp hprim hsq hgp hgr
  have hsL : (sigma - 1) * Real.log x = 499 / 1000 := by
    dsimp [sigma]
    field_simp
    ring
  have hbr : (1 - p.value.re) * Real.log x < 2067 / 10000 := by
    apply (lt_div_iff₀ hL0).mp
    linarith [hp.2.2.1]
  have hbt : (1 - r.value.re) * Real.log x < 2067 / 10000 := by
    apply (lt_div_iff₀ hL0).mp
    linarith [hr.2.2.1]
  have hlowp : Real.log x / (7057 / 10000) < 1 / (sigma - p.value.re) := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith [hp.2.2.2.1])).mpr
    nlinarith
  have hlowr : Real.log x / (7057 / 10000) < 1 / (sigma - r.value.re) := by
    apply (div_lt_div_iff₀ (by norm_num) (by linarith [hr.2.2.2.1])).mpr
    nlinarith
  have hinv : 1 / (sigma - 1) = Real.log x / (499 / 1000) := by
    dsimp [sigma]
    field_simp
    ring
  rw [hinv] at hmother
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  norm_num [div_eq_mul_inv] at hmother hlowp hlowr hk
  nlinarith

def NonquadraticPrimitiveSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :=
  {p : ZeroSlots q alpha y // p.character.IsPrimitive ∧ p.character ^ 2 ≠ 1}

instance nonquadraticPrimitiveSlotsFintype (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype (NonquadraticPrimitiveSlots q alpha y) :=
  inferInstanceAs (Fintype {p : ZeroSlots q alpha y // p.character.IsPrimitive ∧ p.character ^ 2 ≠ 1})

theorem nonquadratic_primitive_slots_card_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    Fintype.card (NonquadraticPrimitiveSlots q (1 - (2067 / 10000) / Real.log x) (x / q)) ≤ 2 := by
  let α := NonquadraticPrimitiveSlots q (1 - (2067 / 10000) / Real.log x) (x / q)
  by_cases h : Nonempty α
  · obtain ⟨p⟩ := h
    have hpc : p.val.character ≠ 1 := by intro he; have := p.property.2; simp [he] at this
    have hmem (r : α) : r.val ∈ ({p.val, conjugateSlot p.val} : Finset _) := by
      have hrc : r.val.character ≠ 1 := by intro he; have := r.property.2; simp [he] at this
      have hh := primitive_slots_same_or_inverse hx hq p.val r.val hpc p.property.1 hrc r.property.1
      rcases hh with hc | hc
      · have he := repeated_label_unique hx hq p.val r.val hc p.property.1 p.property.2
        simp [he]
      · have hc' : p.val.character = (conjugateSlot r.val).character := by
          rw [conjugateSlot_character]
          exact hc
        have he := repeated_label_unique hx hq p.val (conjugateSlot r.val) hc' p.property.1 p.property.2
        have her : r.val = conjugateSlot p.val := by
          have hh := congrArg conjugateSlot he
          rw [conjugateSlot_involutive] at hh
          exact hh.symm
        simp [her]
    let f : α → {r // r ∈ ({p.val, conjugateSlot p.val} : Finset _)} := fun r => ⟨r.val, hmem r⟩
    have hf : Function.Injective f := by
      intro r s he
      apply Subtype.ext
      exact congrArg (fun z : {r // r ∈ ({p.val, conjugateSlot p.val} : Finset _)} => z.val) he
    have hh := Fintype.card_le_of_injective f hf
    have hb := Finset.card_le_two (a := p.val) (b := conjugateSlot p.val)
    simp only [Fintype.card_coe] at hh
    exact hh.trans hb
  · have : IsEmpty α := not_nonempty_iff.mp h
    simpa only [show NonquadraticPrimitiveSlots q (1 - (2067 / 10000) / Real.log x) (x / q) = α from rfl,
      Fintype.card_of_isEmpty] using (show (0 : ℕ) ≤ 2 by norm_num)

def nonquadraticPrimitiveCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi : {chi : DirichletCharacter ℂ q // chi.IsPrimitive ∧ chi ^ 2 ≠ 1},
    ∑ rho ∈ strictZeroValues chi.val alpha y, analyticOrderNatAt chi.val.LFunction rho

def nonquadraticSlotsSigmaEquiv (q : ℕ) [NeZero q] (alpha y : ℝ) :
    NonquadraticPrimitiveSlots q alpha y ≃
      Σ chi : {chi : DirichletCharacter ℂ q // chi.IsPrimitive ∧ chi ^ 2 ≠ 1},
        Σ rho : {rho : ℂ // rho ∈ strictZeroValues chi.val alpha y},
          Fin (analyticOrderNatAt chi.val.LFunction rho.val) where
  toFun p := ⟨⟨p.val.character, p.property⟩,
    ⟨⟨p.val.value, p.val.zero_mem⟩, ⟨p.val.index, p.val.index_lt⟩⟩⟩
  invFun p := ⟨⟨p.1.val, p.2.1.val, p.2.2.val, p.2.1.property, p.2.2.isLt⟩, p.1.property⟩
  left_inv p := by rcases p with ⟨⟨chi, rho, k, hr, hk⟩, hc⟩; rfl
  right_inv p := by rcases p with ⟨⟨chi, hc⟩, ⟨⟨rho, hr⟩, ⟨k, hk⟩⟩⟩; rfl

theorem nonquadraticPrimitiveCount_eq_card (q : ℕ) [NeZero q] (alpha y : ℝ) :
    nonquadraticPrimitiveCount q alpha y = Fintype.card (NonquadraticPrimitiveSlots q alpha y) := by
  rw [Fintype.card_congr (nonquadraticSlotsSigmaEquiv q alpha y)]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_coe_sort, nonquadraticPrimitiveCount]

theorem nonquadraticPrimitiveCount_le_two {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x) :
    nonquadraticPrimitiveCount q (1 - (2067 / 10000) / Real.log x) (x / q) ≤ 2 := by
  rw [nonquadraticPrimitiveCount_eq_card]
  exact nonquadratic_primitive_slots_card_le_two hx hq

end LiuWang.Proof.MultiZeroRepulsion.Continuation
