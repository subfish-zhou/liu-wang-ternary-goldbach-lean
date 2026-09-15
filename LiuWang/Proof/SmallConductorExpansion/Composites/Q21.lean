import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 21 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q21Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), some (1, 0), none, some (0, 2), some (0, 1), none, none, some (1, 2), none, some (1, 1), some (1, 4), none, some (1, 5), none, none, some (0, 4), some (0, 5), none, some (1, 3), some (0, 3)]

theorem q21_cover : UnitWordCover 21 2 5 q21Words := by decide

theorem q21_case0 : (∑ k ∈ range 21, tableValue 21 (wordValues q21Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 21 (wordValues q21Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q21Words, Finset.sum_range_succ]

theorem q21_case1 : (∑ k ∈ range 21, tableValue 21 (wordValues q21Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 21 (wordValues q21Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨3, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q21Words, Finset.sum_range_succ]

theorem q21_case2 : (∑ k ∈ range 21, tableValue 21 (wordValues q21Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 21 (wordValues q21Words (-1) (1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q21Words, Finset.sum_range_succ]

theorem q21_original_region (chi : DirichletCharacter ℂ 21)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 2) (h := 5)
    (by decide) (by decide) q21Words q21_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q21_case0
  · exact q21_case1
  · exact q21_case2

end LiuWang.Proof.SmallConductorExpansion
