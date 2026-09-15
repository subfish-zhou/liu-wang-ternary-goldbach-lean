import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 16 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q16Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, some (1, 0), none, some (0, 1), none, some (1, 3), none, some (0, 2), none, some (1, 2), none, some (0, 3), none, some (1, 1)]

theorem q16_cover : UnitWordCover 16 3 5 q16Words := by decide

theorem q16_case0 : (∑ k ∈ range 16, tableValue 16 (wordValues q16Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 16 (wordValues q16Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q16Words, Finset.sum_range_succ]

theorem q16_case1 : (∑ k ∈ range 16, tableValue 16 (wordValues q16Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 16 (wordValues q16Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q16Words, Finset.sum_range_succ]

theorem q16_case2 : (∑ k ∈ range 16, tableValue 16 (wordValues q16Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 16 (wordValues q16Words (-1) (1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q16Words, Finset.sum_range_succ]

theorem q16_original_region (chi : DirichletCharacter ℂ 16)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 3) (h := 5)
    (by decide) (by decide) q16Words q16_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q16_case0
  · exact q16_case1
  · exact q16_case2

end LiuWang.Proof.SmallConductorExpansion
