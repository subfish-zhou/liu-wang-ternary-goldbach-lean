import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 20 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q20Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, some (1, 0), none, none, none, some (3, 0), none, some (2, 0), none, some (0, 1), none, some (1, 1), none, none, none, some (3, 1), none, some (2, 1)]

theorem q20_cover : UnitWordCover 20 3 11 q20Words := by decide

theorem q20_case0 : (∑ k ∈ range 20, tableValue 20 (wordValues q20Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 20 (wordValues q20Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q20Words, Finset.sum_range_succ]

theorem q20_case1 : (∑ k ∈ range 20, tableValue 20 (wordValues q20Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 20 (wordValues q20Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨4, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q20Words, Finset.sum_range_succ]

theorem q20_case2 : (∑ k ∈ range 20, tableValue 20 (wordValues q20Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 20 (wordValues q20Words (-1) (1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q20Words, Finset.sum_range_succ]

theorem q20_original_region (chi : DirichletCharacter ℂ 20)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 3) (h := 11)
    (by decide) (by decide) q20Words q20_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q20_case0
  · exact q20_case1
  · exact q20_case2

end LiuWang.Proof.SmallConductorExpansion
