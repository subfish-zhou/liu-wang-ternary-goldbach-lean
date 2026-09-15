import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 41, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords41 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (17, 0), some (1, 1), some (2, 0), some (13, 0), some (17, 1), some (4, 1), some (7, 0), some (3, 0), some (16, 0), some (20, 1), some (2, 1), some (10, 1), some (14, 1), some (13, 1), some (4, 0), some (19, 1), some (10, 0), some (15, 1), some (15, 0), some (12, 0), some (12, 1), some (8, 0), some (7, 1), some (5, 0), some (6, 1), some (3, 1), some (8, 1), some (18, 1), some (16, 1), some (20, 0), some (14, 0), some (19, 0), some (5, 1), some (11, 1), some (6, 0), some (18, 0), some (9, 1), some (11, 0), some (9, 0)]

def squareGenerators41 : Fin 1 → ℕ := ![3]

def squareAmplitude41 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 4 else 39)

theorem squareCover41 : SquareWordCover 41 squareGenerators41 squareWords41 := by
  decide +kernel

theorem squareCertificates41 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 41, tableValue 41 (squareValues squareWords41 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 41 (squareValues squareWords41 signs)
        41 (squareAmplitude41 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_41_original_region (chi : DirichletCharacter ℂ 41)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 41 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators41 (by decide +kernel)
    squareWords41 squareCover41 (m := 41) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates41 signs).imp_right fun h => ⟨squareAmplitude41 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
