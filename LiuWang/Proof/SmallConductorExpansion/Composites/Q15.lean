import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 15 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q15Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), some (1, 0), none, some (0, 2), none, none, some (0, 1), some (1, 2), none, none, some (1, 3), none, some (0, 3), some (1, 1)]

theorem q15_cover : UnitWordCover 15 2 7 q15Words := by decide

theorem q15_case0 : (∑ k ∈ range 15, tableValue 15 (wordValues q15Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 15 (wordValues q15Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q15Words, Finset.sum_range_succ]

theorem q15_case1 : (∑ k ∈ range 15, tableValue 15 (wordValues q15Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 15 (wordValues q15Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨3, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q15Words, Finset.sum_range_succ]

theorem q15_case2 : (∑ k ∈ range 15, tableValue 15 (wordValues q15Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 15 (wordValues q15Words (-1) (1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q15Words, Finset.sum_range_succ]

theorem q15_original_region (chi : DirichletCharacter ℂ 15)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 2) (h := 7)
    (by decide) (by decide) q15Words q15_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q15_case0
  · exact q15_case1
  · exact q15_case2

end LiuWang.Proof.SmallConductorExpansion
