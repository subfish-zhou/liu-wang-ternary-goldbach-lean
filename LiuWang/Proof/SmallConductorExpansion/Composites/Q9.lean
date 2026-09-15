import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 9 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q9Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), some (0, 1), none, some (0, 2), some (0, 5), none, some (0, 4), some (0, 3)]

theorem q9_cover : UnitWordCover 9 1 2 q9Words := by decide

theorem q9_case0 : (∑ k ∈ range 9, tableValue 9 (wordValues q9Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 9 (wordValues q9Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q9Words, Finset.sum_range_succ]

theorem q9_case1 : (∑ k ∈ range 9, tableValue 9 (wordValues q9Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 9 (wordValues q9Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q9Words, Finset.sum_range_succ]

theorem q9_case2 : (∑ k ∈ range 9, tableValue 9 (wordValues q9Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 9 (wordValues q9Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q9_original_region (chi : DirichletCharacter ℂ 9)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 2)
    (by decide) (by decide) q9Words q9_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q9_case0
  · exact q9_case1
  · exact q9_case2

end LiuWang.Proof.SmallConductorExpansion
