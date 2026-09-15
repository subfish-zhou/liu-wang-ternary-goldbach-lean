import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 12 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q12Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, none, none, some (1, 0), none, some (0, 1), none, none, none, some (1, 1)]

theorem q12_cover : UnitWordCover 12 5 7 q12Words := by decide

theorem q12_case0 : (∑ k ∈ range 12, tableValue 12 (wordValues q12Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 12 (wordValues q12Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q12Words, Finset.sum_range_succ]

theorem q12_case1 : (∑ k ∈ range 12, tableValue 12 (wordValues q12Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 12 (wordValues q12Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q12Words, Finset.sum_range_succ]

theorem q12_case2 : (∑ k ∈ range 12, tableValue 12 (wordValues q12Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 12 (wordValues q12Words (-1) (1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q12Words, Finset.sum_range_succ]

theorem q12_original_region (chi : DirichletCharacter ℂ 12)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 5) (h := 7)
    (by decide) (by decide) q12Words q12_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q12_case0
  · exact q12_case1
  · exact q12_case2

end LiuWang.Proof.SmallConductorExpansion
