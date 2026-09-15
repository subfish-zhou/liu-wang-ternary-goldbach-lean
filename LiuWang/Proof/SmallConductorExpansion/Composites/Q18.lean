import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 18 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q18Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, none, none, some (0, 1), none, some (0, 2), none, none, none, some (0, 5), none, some (0, 4), none, none, none, some (0, 3)]

theorem q18_cover : UnitWordCover 18 1 5 q18Words := by decide

theorem q18_case0 : (∑ k ∈ range 18, tableValue 18 (wordValues q18Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 18 (wordValues q18Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q18Words, Finset.sum_range_succ]

theorem q18_case1 : (∑ k ∈ range 18, tableValue 18 (wordValues q18Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 18 (wordValues q18Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q18Words, Finset.sum_range_succ]

theorem q18_case2 : (∑ k ∈ range 18, tableValue 18 (wordValues q18Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 18 (wordValues q18Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q18_original_region (chi : DirichletCharacter ℂ 18)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 5)
    (by decide) (by decide) q18Words q18_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q18_case0
  · exact q18_case1
  · exact q18_case2

end LiuWang.Proof.SmallConductorExpansion
