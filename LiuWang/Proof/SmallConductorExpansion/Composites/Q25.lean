import LiuWang.Proof.SmallConductorExpansion.UnitWords

/-! # Exact unit-word coverage and signed certificates modulo 25 -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion

def q25Words : List (Option (ℕ × ℕ)) := [none, some (0, 0), some (0, 1), some (0, 7), some (0, 2), none, some (0, 8), some (0, 5), some (0, 3), some (0, 14), none, some (0, 16), some (0, 9), some (0, 19), some (0, 6), none, some (0, 4), some (0, 13), some (0, 15), some (0, 18), none, some (0, 12), some (0, 17), some (0, 11), some (0, 10)]

theorem q25_cover : UnitWordCover 25 1 2 q25Words := by decide

theorem q25_case0 : (∑ k ∈ range 25, tableValue 25 (wordValues q25Words (-1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 25 (wordValues q25Words (-1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q25Words, Finset.sum_range_succ]

theorem q25_case1 : (∑ k ∈ range 25, tableValue 25 (wordValues q25Words (1) (-1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 25 (wordValues q25Words (1) (-1)) 32 P (6 / 5) := by
  right
  refine ⟨1, ?_, ?_⟩
  · decide
  · norm_num [tableValue, wordValues, q25Words, Finset.sum_range_succ]

theorem q25_case2 : (∑ k ∈ range 25, tableValue 25 (wordValues q25Words (-1) (1)) k) ≠ 0 ∨
      ∃ P : ℚ, RationalCertificate 25 (wordValues q25Words (-1) (1)) 32 P (6 / 5) := by
  left
  decide

theorem q25_original_region (chi : DirichletCharacter ℂ 25)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply unit_word_original_region chi hc hsq (g := 1) (h := 2)
    (by decide) (by decide) q25Words q25_cover _ hx hb
  intro a b hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact q25_case0
  · exact q25_case1
  · exact q25_case2

end LiuWang.Proof.SmallConductorExpansion
