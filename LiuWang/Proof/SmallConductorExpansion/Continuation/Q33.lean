import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 33, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords33 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, some (2, 3), some (2, 1), none, some (1, 3), none, none, some (8, 3), some (4, 2), none, some (4, 0), some (5, 1), none, some (5, 3), some (2, 2), none, none, some (8, 2), none, some (5, 0), some (5, 2), none, some (4, 3), some (8, 1), none, some (8, 0), some (4, 1)]

def squareGenerators33 : Fin 2 → ℕ := ![2, 5]

def squareAmplitude33 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 2) else (if signs 1 then 3 else 19))

theorem squareCover33 : SquareWordCover 33 squareGenerators33 squareWords33 := by
  decide +kernel

theorem squareCertificates33 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 33, tableValue 33 (squareValues squareWords33 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 33 (squareValues squareWords33 signs)
        33 (squareAmplitude33 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_33_original_region (chi : DirichletCharacter ℂ 33)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 33 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators33 (by decide +kernel)
    squareWords33 squareCover33 (m := 33) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates33 signs).imp_right fun h => ⟨squareAmplitude33 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
