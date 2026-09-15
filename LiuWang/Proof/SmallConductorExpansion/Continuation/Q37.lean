import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 37, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords37 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (15, 0), some (2, 0), some (13, 1), some (15, 1), some (9, 0), some (2, 1), some (3, 0), some (11, 0), some (14, 0), some (7, 0), some (5, 1), some (9, 1), some (10, 1), some (4, 0), some (8, 1), some (3, 1), some (18, 1), some (11, 1), some (13, 0), some (14, 1), some (17, 1), some (7, 1), some (5, 0), some (10, 0), some (8, 0), some (18, 0), some (12, 1), some (17, 0), some (16, 1), some (4, 1), some (12, 0), some (16, 0), some (6, 1), some (6, 0)]

def squareGenerators37 : Fin 1 → ℕ := ![2]

def squareAmplitude37 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 4 else 35)

theorem squareCover37 : SquareWordCover 37 squareGenerators37 squareWords37 := by
  decide +kernel

theorem squareCertificates37 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 37, tableValue 37 (squareValues squareWords37 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 37 (squareValues squareWords37 signs)
        37 (squareAmplitude37 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_37_original_region (chi : DirichletCharacter ℂ 37)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 37 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators37 (by decide +kernel)
    squareWords37 squareCover37 (m := 37) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates37 signs).imp_right fun h => ⟨squareAmplitude37 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
