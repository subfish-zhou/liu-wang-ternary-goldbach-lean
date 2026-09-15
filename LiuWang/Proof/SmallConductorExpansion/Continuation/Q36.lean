import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 36, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords36 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, some (5, 3), none, some (7, 0), none, none, none, some (5, 1), none, some (7, 2), none, none, none, some (7, 3), none, some (5, 0), none, none, none, some (7, 1), none, some (5, 2), none, none, none, some (1, 3)]

def squareGenerators36 : Fin 2 → ℕ := ![5, 7]

def squareAmplitude36 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 1) else (if signs 1 then 2 else 11))

theorem squareCover36 : SquareWordCover 36 squareGenerators36 squareWords36 := by
  decide +kernel

theorem squareCertificates36 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 36, tableValue 36 (squareValues squareWords36 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 36 (squareValues squareWords36 signs)
        36 (squareAmplitude36 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_36_original_region (chi : DirichletCharacter ℂ 36)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 36 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators36 (by decide +kernel)
    squareWords36 squareCover36 (m := 36) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates36 signs).imp_right fun h => ⟨squareAmplitude36 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
