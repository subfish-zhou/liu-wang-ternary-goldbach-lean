import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 26 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q26Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, some (0, 8), none, some (0, 3), none, some (0, 1), none, some (0, 4), none, some (0, 5), none, none, none, some (0, 11), none, some (0, 10), none, some (0, 7), none, some (0, 9), none, some (0, 2), none, some (0, 6)]

theorem q26_cover : UnitWordCover 26 1 7 q26Words := by decide

theorem q26_case0 : (∑ k ∈ range 26, tableValue 26 (wordValues q26Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 26 (wordValues q26Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q26Words, Finset.sum_range_succ]

theorem q26_case1 : (∑ k ∈ range 26, tableValue 26 (wordValues q26Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 26 (wordValues q26Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q26Words, Finset.sum_range_succ]

theorem q26_case2 : (∑ k ∈ range 26, tableValue 26 (wordValues q26Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 26 (wordValues q26Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q26_original_region (chi : DirichletCharacter ℂ 26)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 7)
    (by decide) (by decide) q26Words q26_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q26_case0
  · exact q26_case1
  · exact q26_case2

end LiuWang.Proof.SmallConductorExpansion
