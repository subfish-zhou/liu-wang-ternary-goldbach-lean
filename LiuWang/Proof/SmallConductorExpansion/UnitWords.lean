import LiuWang.Proof.SmallConductorExpansion.Tables

/-!
# Exhaustive finite quadratic-character classification from unit words

Each residue is either certified nonunit or represented as a word in two
specified units. Their character values must be signs. Thus the three
nonprincipal sign assignments exhaust every actual quadratic character,
without assuming a conductor/discriminant table.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def wordValues (words : List (Option (ℕ × ℕ))) (a b : ℤ) : List ℤ :=
  words.map fun w => match w with
    | none => 0
    | some (i, j) => a ^ i * b ^ j

def UnitWordCover (q g h : ℕ) (words : List (Option (ℕ × ℕ))) : Prop :=
  ∀ z : ZMod q, match words.getD z.val none with
    | none => ¬IsUnit z
    | some (i, j) => z = (g : ZMod q) ^ i * (h : ZMod q) ^ j

instance unitWordCoverDecidable (q g h : ℕ) [NeZero q]
    (words : List (Option (ℕ × ℕ))) : Decidable (UnitWordCover q g h words) := by
  unfold UnitWordCover
  letI (z : ZMod q) : Decidable (match words.getD z.val none with
      | none => ¬IsUnit z
      | some (i, j) => z = (g : ZMod q) ^ i * (h : ZMod q) ^ j) := by
    split <;> infer_instance
  infer_instance

theorem wordValues_getD (words : List (Option (ℕ × ℕ))) (a b : ℤ) (n : ℕ) :
    (wordValues words a b).getD n 0 =
      match words.getD n none with
      | none => 0
      | some (i, j) => a ^ i * b ^ j := by
  simp only [wordValues, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases words[n]? with
  | none => rfl
  | some w => cases w <;> rfl

theorem word_character_table {q g h : ℕ} (chi : DirichletCharacter ℂ q)
    (words : List (Option (ℕ × ℕ))) (hcover : UnitWordCover q g h words)
    {a b : ℤ} (ha : chi g = (a : ℂ)) (hb : chi h = (b : ℂ)) :
    ∀ z : ZMod q, chi z = ((wordValues words a b).getD z.val 0 : ℂ) := by
  intro z
  rw [wordValues_getD]
  have hz := hcover z
  cases hw : words.getD z.val none with
  | none =>
      simp only [hw] at hz ⊢
      rw [MulChar.map_nonunit chi hz]
      simp
  | some w =>
      rcases w with ⟨i, j⟩
      simp only [hw] at hz ⊢
      rw [hz, map_mul, map_pow, map_pow, ha, hb]
      push_cast
      rfl

theorem unit_word_all_one {q g h : ℕ} (chi : DirichletCharacter ℂ q)
    (words : List (Option (ℕ × ℕ))) (hcover : UnitWordCover q g h words)
    (ha : chi g = 1) (hb : chi h = 1) : chi = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.one_apply_coe]
  have hz := hcover (u : ZMod q)
  cases hw : words.getD (u : ZMod q).val none with
  | none =>
      rw [hw] at hz
      exact (hz u.isUnit).elim
  | some w =>
      rcases w with ⟨i, j⟩
      simp only [hw] at hz
      rw [hz, map_mul, map_pow, map_pow, ha, hb, one_pow, one_pow, mul_one]

theorem unit_word_signs {q g h : ℕ} (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    (hg : IsUnit (g : ZMod q)) (hh : IsUnit (h : ZMod q))
    (words : List (Option (ℕ × ℕ))) (hcover : UnitWordCover q g h words) :
    (chi g = -1 ∧ chi h = -1) ∨
      (chi g = 1 ∧ chi h = -1) ∨ (chi g = -1 ∧ chi h = 1) := by
  have ha := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq (g : ZMod q)
  have hb := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq (h : ZMod q)
  have haz : chi g ≠ 0 := (hg.map chi).ne_zero
  have hbz : chi h ≠ 0 := (hh.map chi).ne_zero
  rcases ha with ha | ha | ha
  · exact (haz ha).elim
  · rcases hb with hb | hb | hb
    · exact (hbz hb).elim
    · exact (hc (unit_word_all_one chi words hcover ha hb)).elim
    · exact Or.inr (Or.inl ⟨ha, hb⟩)
  · rcases hb with hb | hb | hb
    · exact (hbz hb).elim
    · exact Or.inr (Or.inr ⟨ha, hb⟩)
    · exact Or.inl ⟨ha, hb⟩

theorem unit_word_original_region {q g h : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    (hg : IsUnit (g : ZMod q)) (hh : IsUnit (h : ZMod q))
    (words : List (Option (ℕ × ℕ))) (hcover : UnitWordCover q g h words)
    (hcert : ∀ (a b : ℤ), (a = -1 ∧ b = -1) ∨ (a = 1 ∧ b = -1) ∨
      (a = -1 ∧ b = 1) →
      (∑ k ∈ range q, tableValue q (wordValues words a b) k) ≠ 0 ∨
        ∃ P : ℚ, RationalCertificate q (wordValues words a b) 32 P (6 / 5))
    {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have huse (a b : ℤ) (ha : chi g = (a : ℂ)) (hb' : chi h = (b : ℂ))
      (hab : (a = -1 ∧ b = -1) ∨ (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1)) :
      chi.LFunction (beta : ℂ) ≠ 0 := by
    have htable := word_character_table chi words hcover ha hb'
    rcases hcert a b hab with hsum | ⟨P, hP⟩
    · have hz := DirichletLWeakStripDerivative.sum_one_period_eq_zero chi hc
      simp only [tableValue_character chi _ htable, ← Int.cast_sum] at hz
      exact False.elim (hsum (by exact_mod_cast hz))
    · exact rationalCertificate_original_region chi hc (wordValues words a b)
        htable (by decide) (by decide) hP hx hb
  rcases unit_word_signs chi hc hsq hg hh words hcover with ⟨ha, hb'⟩ | ⟨ha, hb'⟩ | ⟨ha, hb'⟩
  · exact huse (-1) (-1) (by simpa using ha) (by simpa using hb') (by simp)
  · exact huse 1 (-1) (by simpa using ha) (by simpa using hb') (by simp)
  · exact huse (-1) 1 (by simpa using ha) (by simpa using hb') (by simp)

end LiuWang.Proof.SmallConductorExpansion
