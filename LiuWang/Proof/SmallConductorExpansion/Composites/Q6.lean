import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 6 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q6Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), none, none, none, some (0, 1)]

theorem q6_cover : UnitWordCover 6 1 5 q6Words := by decide

theorem q6_case0 : (∑ k ∈ range 6, tableValue 6 (wordValues q6Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 6 (wordValues q6Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q6Words, Finset.sum_range_succ]

theorem q6_case1 : (∑ k ∈ range 6, tableValue 6 (wordValues q6Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 6 (wordValues q6Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q6Words, Finset.sum_range_succ]

theorem q6_case2 : (∑ k ∈ range 6, tableValue 6 (wordValues q6Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 6 (wordValues q6Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q6_original_region (chi : DirichletCharacter ℂ 6)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 5)
    (by decide) (by decide) q6Words q6_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q6_case0
  · exact q6_case1
  · exact q6_case2

end LiuWang.Proof.SmallConductorExpansion
