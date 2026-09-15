import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 10 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q10Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, some (0, 1), none, none, none, some (0, 3), none, some (0, 2)]

theorem q10_cover : UnitWordCover 10 1 3 q10Words := by decide

theorem q10_case0 : (∑ k ∈ range 10, tableValue 10 (wordValues q10Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 10 (wordValues q10Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q10Words, Finset.sum_range_succ]

theorem q10_case1 : (∑ k ∈ range 10, tableValue 10 (wordValues q10Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 10 (wordValues q10Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q10Words, Finset.sum_range_succ]

theorem q10_case2 : (∑ k ∈ range 10, tableValue 10 (wordValues q10Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 10 (wordValues q10Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q10_original_region (chi : DirichletCharacter ℂ 10)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 3)
    (by decide) (by decide) q10Words q10_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q10_case0
  · exact q10_case1
  · exact q10_case2

end LiuWang.Proof.SmallConductorExpansion
