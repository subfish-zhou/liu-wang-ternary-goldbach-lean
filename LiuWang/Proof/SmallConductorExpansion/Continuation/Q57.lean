import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 57, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords57 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, some (8, 0), some (2, 1), none, some (1, 3), some (5, 2), none, some (8, 3), some (8, 1), none, some (4, 0), some (7, 2), none, none, some (2, 2), none, some (5, 3), some (4, 2), none, some (5, 0), some (16, 2), none, some (16, 0), some (10, 1), none, some (10, 3), some (4, 1), none, some (7, 3), some (8, 2), none, some (13, 3), none, none, some (2, 3), some (7, 1), none, some (10, 0), some (10, 2), none, some (4, 3), some (13, 2), none, some (7, 0), some (5, 1), none, some (16, 3), some (13, 1), none, some (13, 0), some (16, 1)]

def squareGenerators57 : Fin 2 → ℕ := ![2, 5]

def squareAmplitude57 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 6) else (if signs 1 then 4 else 35))

theorem squareCover57 : SquareWordCover 57 squareGenerators57 squareWords57 := by
  decide +kernel

theorem squareCertificates57 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 57, tableValue 57 (squareValues squareWords57 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 57 (squareValues squareWords57 signs)
        57 (squareAmplitude57 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_57_original_region (chi : DirichletCharacter ℂ 57)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 57 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators57 (by decide +kernel)
    squareWords57 squareCover57 (m := 57) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates57 signs).imp_right fun h => ⟨squareAmplitude57 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
