import LiuWang.Proof.DirichletZeroCount.Principal

/-!
# The actual full character family, with principal and conductor budgets

No count estimate is an input field. The normalized statement divides by the
actual `phi(q)`, and the principal contribution occurs exactly once.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.DirichletZeroCount

def nonprincipalBound (d : ℕ) (y : ℝ) : ℝ :=
  (2 * y + 3) * (Real.log d / 2 + Real.log (y + 3) / 2 + 5 / 4)

theorem nonprincipalBound_mono {d q : ℕ} (hd : 0 < d) (hdq : d ≤ q)
    {y : ℝ} (hy : 0 ≤ y) :
    nonprincipalBound d y ≤ nonprincipalBound q y := by
  have hl := Real.log_le_log (Nat.cast_pos.mpr hd)
    (Nat.cast_le.mpr hdq : (d : ℝ) ≤ q)
  unfold nonprincipalBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem count_le_conductor {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ nonprincipalBound chi.conductor y :=
  count_conductor_linear hchi alpha hy

theorem count_le_modulus {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ nonprincipalBound q y :=
  (count_le_conductor hchi alpha hy).trans
    (nonprincipalBound_mono (Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy)

def characterBound {q : ℕ} [NeZero q] (chi : Character q) (y : ℝ) : ℝ :=
  if chi = 1 then principalBound y else nonprincipalBound chi.conductor y

theorem count_le_characterBound {q : ℕ} [NeZero q] (chi : Character q)
    (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (count chi alpha y : ℝ) ≤ characterBound chi y := by
  unfold characterBound
  split_ifs with h
  · subst chi
    exact count_principal_le q alpha hy
  · exact count_le_conductor h alpha hy

theorem characterBound_nonneg {q : ℕ} [NeZero q] (chi : Character q)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ characterBound chi y :=
  (Nat.cast_nonneg (count chi 0 y)).trans (count_le_characterBound chi 0 hy)

def familyCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi : Character q, count chi alpha y

def familyBound (q : ℕ) [NeZero q] (y : ℝ) : ℝ :=
  principalBound y +
    ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, nonprincipalBound chi.conductor y

theorem sum_characterBound (q : ℕ) [NeZero q] (y : ℝ) :
    (∑ chi : Character q, characterBound chi y) = familyBound q y := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q))]
  unfold familyBound
  have he : (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
      characterBound chi y) =
      ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        nonprincipalBound chi.conductor y := by
    apply Finset.sum_congr rfl
    intro chi hc
    simp only [characterBound, if_neg (Finset.mem_erase.mp hc).1]
  rw [he]
  simp only [characterBound, ↓reduceIte]
  ring

theorem familyCount_le (q : ℕ) [NeZero q] (alpha : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ familyBound q y := by
  unfold familyCount
  rw [Nat.cast_sum, ← sum_characterBound]
  exact Finset.sum_le_sum (fun chi _ => count_le_characterBound chi alpha hy)

theorem familyBound_le_modulus (q : ℕ) [NeZero q] {y : ℝ} (hy : 0 ≤ y) :
    familyBound q y ≤ principalBound y + (q.totient - 1 : ℕ) * nonprincipalBound q y := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold familyBound
  apply add_le_add_right
  calc
    _ ≤ ∑ _chi ∈ (Finset.univ : Finset (Character q)).erase 1,
        nonprincipalBound q y := by
      apply Finset.sum_le_sum
      intro chi _
      exact nonprincipalBound_mono (Nat.pos_of_ne_zero chi.conductor_ne_zero)
        (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy
    _ = _ := by simp [hc]

theorem normalized_familyCount_le (q : ℕ) [NeZero q] (alpha : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (familyCount q alpha y : ℝ) / q.totient ≤
      (principalBound y + (q.totient - 1 : ℕ) * nonprincipalBound q y) / q.totient := by
  exact div_le_div_of_nonneg_right
    ((familyCount_le q alpha hy).trans (familyBound_le_modulus q hy)) (Nat.cast_nonneg _)

end LiuWang.Proof.DirichletZeroCount
