import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 45, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords45 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), none, none, some (1, 2), some (2, 1), none, none, some (2, 3), none, some (13, 2), some (1, 3), none, some (4, 0), some (11, 1), none, some (8, 0), none, none, some (4, 2), some (13, 1), none, none, some (13, 3), none, some (2, 2), some (11, 3), none, some (11, 0), some (4, 1), none, some (13, 0), none, none, some (11, 2), some (8, 1), none, none, some (8, 3), none, some (8, 2), some (4, 3)]

def squareGenerators45 : Fin 2 → ℕ := ![2, 7]

def squareAmplitude45 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 2) else (if signs 1 then 3 else 23))

theorem squareCover45 : SquareWordCover 45 squareGenerators45 squareWords45 := by
  decide +kernel

theorem squareCertificates45 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 45, tableValue 45 (squareValues squareWords45 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 45 (squareValues squareWords45 signs)
        45 (squareAmplitude45 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_45_original_region (chi : DirichletCharacter ℂ 45)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 45 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators45 (by decide +kernel)
    squareWords45 squareCover45 (m := 45) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates45 signs).imp_right fun h => ⟨squareAmplitude45 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
