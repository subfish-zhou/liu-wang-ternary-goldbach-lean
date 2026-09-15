import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 27 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q27Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), some (0, 1), none, some (0, 2), some (0, 5), none, some (0, 16), some (0, 3), none, some (0, 6), some (0, 13), none, some (0, 8), some (0, 17), none, some (0, 4), some (0, 15), none, some (0, 12), some (0, 7), none, some (0, 14), some (0, 11), none, some (0, 10), some (0, 9)]

theorem q27_cover : UnitWordCover 27 1 2 q27Words := by decide

theorem q27_case0 : (∑ k ∈ range 27, tableValue 27 (wordValues q27Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 27 (wordValues q27Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q27Words, Finset.sum_range_succ]

theorem q27_case1 : (∑ k ∈ range 27, tableValue 27 (wordValues q27Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 27 (wordValues q27Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q27Words, Finset.sum_range_succ]

theorem q27_case2 : (∑ k ∈ range 27, tableValue 27 (wordValues q27Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 27 (wordValues q27Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q27_original_region (chi : DirichletCharacter ℂ 27)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 2)
    (by decide) (by decide) q27Words q27_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q27_case0
  · exact q27_case1
  · exact q27_case2

end LiuWang.Proof.SmallConductorExpansion
