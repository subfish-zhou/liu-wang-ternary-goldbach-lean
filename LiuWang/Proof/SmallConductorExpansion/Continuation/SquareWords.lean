import LiuWang.Proof.SmallConductorExpansion.Continuation.Weighted

/-!
# Exhaustive quadratic-character tables from square cosets

A square-coset cover uses any finite number of unit generators. Every actual
quadratic character is recovered from their signs; finite verification covers
all sign assignments, including assignments incompatible with nonprincipality.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWord {d : ℕ} (q : ℕ) (gs : Fin d → ℕ) (mask : ℕ) : ZMod q :=
  ∏ i, if mask.testBit i.val then (gs i : ZMod q) else 1

def signedWord {d : ℕ} (signs : Fin d → Bool) (mask : ℕ) : ℤ :=
  ∏ i, if mask.testBit i.val then (if signs i then -1 else 1) else 1

def squareValues {d : ℕ} (words : List (Option (ℕ × ℕ)))
    (signs : Fin d → Bool) : List ℤ :=
  words.map fun w => match w with
    | none => 0
    | some (_, mask) => signedWord signs mask

def SquareWordCover {d : ℕ} (q : ℕ) (gs : Fin d → ℕ)
    (words : List (Option (ℕ × ℕ))) : Prop :=
  ∀ z : ZMod q, match words.getD z.val none with
    | none => ¬IsUnit z
    | some (s, mask) => IsUnit (s : ZMod q) ∧ z = (s : ZMod q) ^ 2 * squareWord q gs mask

instance squareWordCoverDecidable {d : ℕ} (q : ℕ) [NeZero q] (gs : Fin d → ℕ)
    (words : List (Option (ℕ × ℕ))) : Decidable (SquareWordCover q gs words) := by
  unfold SquareWordCover
  letI (z : ZMod q) : Decidable (match words.getD z.val none with
      | none => ¬IsUnit z
      | some (s, mask) => IsUnit (s : ZMod q) ∧
          z = (s : ZMod q) ^ 2 * squareWord q gs mask) := by
    split <;> infer_instance
  infer_instance

theorem squareValues_getD {d : ℕ} (words : List (Option (ℕ × ℕ)))
    (signs : Fin d → Bool) (n : ℕ) :
    (squareValues words signs).getD n 0 =
      match words.getD n none with
      | none => 0
      | some (_, mask) => signedWord signs mask := by
  simp only [squareValues, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases words[n]? with
  | none => rfl
  | some w => cases w <;> rfl

theorem square_word_table {q d : ℕ} (chi : DirichletCharacter ℂ q)
    (hsq : chi ^ 2 = 1) (gs : Fin d → ℕ)
    (words : List (Option (ℕ × ℕ))) (hcover : SquareWordCover q gs words)
    (signs : Fin d → Bool)
    (hs : ∀ i, chi (gs i) = (if signs i then (-1 : ℂ) else 1)) :
    ∀ z : ZMod q, chi z = ((squareValues words signs).getD z.val 0 : ℂ) := by
  intro z
  rw [squareValues_getD]
  have hz := hcover z
  cases hw : words.getD z.val none with
  | none =>
      simp only [hw] at hz ⊢
      rw [MulChar.map_nonunit chi hz]
      simp
  | some w =>
      rcases w with ⟨s, mask⟩
      simp only [hw] at hz ⊢
      have hnonzero : chi s ≠ 0 := (hz.1.map chi).ne_zero
      have hsquare : chi s ^ 2 = 1 := by
        rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq (s : ZMod q) with h | h | h
        · exact (hnonzero h).elim
        · simp [h]
        · simp [h]
      rw [hz.2, map_mul, map_pow, hsquare, one_mul]
      unfold squareWord signedWord
      rw [map_prod, Int.cast_prod]
      apply prod_congr rfl
      intro i _
      cases mask.testBit i.val <;> cases hi : signs i <;> simp [hi, hs i]

theorem square_word_signs {q d : ℕ} (chi : DirichletCharacter ℂ q)
    (hsq : chi ^ 2 = 1) (gs : Fin d → ℕ) (hg : ∀ i, IsUnit (gs i : ZMod q)) :
    ∃ signs : Fin d → Bool, ∀ i, chi (gs i) = (if signs i then (-1 : ℂ) else 1) := by
  classical
  refine ⟨fun i => decide (chi (gs i) = -1), ?_⟩
  intro i
  have hn : chi (gs i) ≠ 0 := ((hg i).map chi).ne_zero
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq (gs i : ZMod q) with h | h | h
  · exact (hn h).elim
  · simp [h]
  · simp [h]

theorem square_word_original_region {q d : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    (gs : Fin d → ℕ) (hg : ∀ i, IsUnit (gs i : ZMod q))
    (words : List (Option (ℕ × ℕ))) (hcover : SquareWordCover q gs words)
    {m n : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) (hn : 1 < n)
    {A : ℚ} (hA : 0 ≤ A) (hpow : 2 ≤ A ^ n)
    (hcert : ∀ signs : Fin d → Bool,
      (∑ k ∈ range q, tableValue q (squareValues words signs) k) ≠ 0 ∨
        ∃ P : ℚ, RationalWeightedCertificate q (squareValues words signs) m P A)
    {x beta : ℝ} (hlog : (n : ℝ) ≤ 9.645908801 * Real.log x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  obtain ⟨signs, hs⟩ := square_word_signs chi hsq gs hg
  have ht := square_word_table chi hsq gs words hcover signs hs
  rcases hcert signs with hsum | ⟨P, hP⟩
  · have hz := DirichletLWeakStripDerivative.sum_one_period_eq_zero chi hc
    simp only [tableValue_character chi _ ht, ← Int.cast_sum] at hz
    exact False.elim (hsum (by exact_mod_cast hz))
  · exact rationalWeighted_original_region chi hc (squareValues words signs) ht
      hm hqm hn hP hA hpow hlog hb

end LiuWang.Proof.SmallConductorExpansion.Continuation
