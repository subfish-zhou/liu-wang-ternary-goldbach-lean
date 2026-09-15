import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 14 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q14Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, some (0, 1), none, some (0, 5), none, none, none, some (0, 2), none, some (0, 4), none, some (0, 3)]

theorem q14_cover : UnitWordCover 14 1 3 q14Words := by decide

theorem q14_case0 : (∑ k ∈ range 14, tableValue 14 (wordValues q14Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 14 (wordValues q14Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q14Words, Finset.sum_range_succ]

theorem q14_case1 : (∑ k ∈ range 14, tableValue 14 (wordValues q14Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 14 (wordValues q14Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q14Words, Finset.sum_range_succ]

theorem q14_case2 : (∑ k ∈ range 14, tableValue 14 (wordValues q14Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 14 (wordValues q14Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q14_original_region (chi : DirichletCharacter ℂ 14)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 3)
    (by decide) (by decide) q14Words q14_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q14_case0
  · exact q14_case1
  · exact q14_case2

end LiuWang.Proof.SmallConductorExpansion
