import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 51, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords51 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, some (4, 3), some (2, 1), none, some (1, 3), some (14, 2), none, some (8, 0), some (8, 2), none, some (4, 0), none, none, some (11, 0), some (2, 2), none, some (14, 3), some (5, 2), none, some (5, 0), some (8, 1), none, some (8, 3), some (4, 2), none, some (7, 3), some (4, 1), none, none, some (14, 1), none, some (11, 3), some (11, 1), none, some (2, 3), some (7, 2), none, some (14, 0), some (11, 2), none, some (5, 3), some (7, 1), none, some (7, 0), some (5, 1)]

def squareGenerators51 : Fin 2 → ℕ := ![2, 5]

def squareAmplitude51 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 6) else (if signs 1 then 3 else 31))

theorem squareCover51 : SquareWordCover 51 squareGenerators51 squareWords51 := by
  decide +kernel

theorem squareCertificates51 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 51, tableValue 51 (squareValues squareWords51 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 51 (squareValues squareWords51 signs)
        51 (squareAmplitude51 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_51_original_region (chi : DirichletCharacter ℂ 51)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 51 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators51 (by decide +kernel)
    squareWords51 squareCover51 (m := 51) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates51 signs).imp_right fun h => ⟨squareAmplitude51 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
