import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 39, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords39 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (10, 1), none, some (1, 2), some (2, 1), none, some (7, 0), some (5, 1), none, none, some (1, 3), none, some (4, 0), some (2, 3), none, some (5, 2), some (7, 1), none, some (10, 0), some (7, 3), none, some (5, 0), none, none, some (2, 2), some (4, 3), none, some (7, 2), some (4, 1), none, some (4, 2), some (10, 3), none, some (10, 2), some (5, 3)]

def squareGenerators39 : Fin 2 → ℕ := ![2, 7]

def squareAmplitude39 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 1) else (if signs 1 then 6 else 23))

theorem squareCover39 : SquareWordCover 39 squareGenerators39 squareWords39 := by
  decide +kernel

theorem squareCertificates39 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 39, tableValue 39 (squareValues squareWords39 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 39 (squareValues squareWords39 signs)
        39 (squareAmplitude39 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_39_original_region (chi : DirichletCharacter ℂ 39)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 39 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators39 (by decide +kernel)
    squareWords39 squareCover39 (m := 39) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates39 signs).imp_right fun h => ⟨squareAmplitude39 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
