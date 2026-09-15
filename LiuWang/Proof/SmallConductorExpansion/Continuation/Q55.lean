import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 55, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords55 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), none, some (1, 3), some (14, 1), some (2, 1), some (3, 0), none, none, some (2, 2), some (12, 1), some (17, 0), none, some (4, 0), some (6, 1), some (3, 1), some (7, 3), none, some (14, 3), none, some (9, 2), some (2, 3), none, some (9, 0), some (3, 2), some (17, 1), some (17, 3), none, some (14, 0), some (4, 1), none, some (12, 0), none, some (6, 0), some (7, 2), some (14, 2), some (12, 3), none, some (4, 3), some (17, 2), some (7, 1), none, none, some (9, 3), some (12, 2), some (4, 2), some (7, 0), none, some (6, 3), some (9, 1), some (6, 2), some (3, 3)]

def squareGenerators55 : Fin 2 → ℕ := ![2, 3]

def squareAmplitude55 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 2) else (if signs 1 then 8 else 39))

theorem squareCover55 : SquareWordCover 55 squareGenerators55 squareWords55 := by
  decide +kernel

theorem squareCertificates55 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 55, tableValue 55 (squareValues squareWords55 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 55 (squareValues squareWords55 signs)
        55 (squareAmplitude55 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_55_original_region (chi : DirichletCharacter ℂ 55)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 55 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators55 (by decide +kernel)
    squareWords55 squareCover55 (m := 55) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates55 signs).imp_right fun h => ⟨squareAmplitude55 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
