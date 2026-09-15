import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 54, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords54 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (13, 0), none, none, none, some (11, 1), none, some (11, 0), none, none, none, some (5, 1), none, some (17, 0), none, none, none, some (19, 1), none, some (5, 0), none, none, none, some (7, 1), none, some (25, 0), none, none, none, some (13, 1), none, some (19, 0), none, none, none, some (17, 1), none, some (23, 0), none, none, none, some (25, 1), none, some (7, 0), none, none, none, some (23, 1)]

def squareGenerators54 : Fin 1 → ℕ := ![5]

def squareAmplitude54 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 1 else 17)

theorem squareCover54 : SquareWordCover 54 squareGenerators54 squareWords54 := by
  decide +kernel

theorem squareCertificates54 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 54, tableValue 54 (squareValues squareWords54 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 54 (squareValues squareWords54 signs)
        54 (squareAmplitude54 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_54_original_region (chi : DirichletCharacter ℂ 54)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 54 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators54 (by decide +kernel)
    squareWords54 squareCover54 (m := 54) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates54 signs).imp_right fun h => ⟨squareAmplitude54 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
