import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 30 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q30Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, none, none, none, none, some (1, 0), none, none, none, some (0, 1), none, some (3, 0), none, none, none, some (1, 1), none, some (2, 0), none, none, none, some (3, 1), none, none, none, none, none, some (2, 1)]

theorem q30_cover : UnitWordCover 30 7 11 q30Words := by decide

theorem q30_case0 : (∑ k ∈ range 30, tableValue 30 (wordValues q30Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 30 (wordValues q30Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q30Words, Finset.sum_range_succ]

theorem q30_case1 : (∑ k ∈ range 30, tableValue 30 (wordValues q30Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 30 (wordValues q30Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨2, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q30Words, Finset.sum_range_succ]

theorem q30_case2 : (∑ k ∈ range 30, tableValue 30 (wordValues q30Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 30 (wordValues q30Words (-1) (1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q30Words, Finset.sum_range_succ]

theorem q30_original_region (chi : DirichletCharacter ℂ 30)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 7) (h := 11)
    (by decide) (by decide) q30Words q30_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q30_case0
  · exact q30_case1
  · exact q30_case2

end LiuWang.Proof.SmallConductorExpansion
