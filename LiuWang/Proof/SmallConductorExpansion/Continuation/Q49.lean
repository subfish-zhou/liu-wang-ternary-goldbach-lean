import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 49, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords49 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (10, 0), some (1, 1), some (2, 0), some (19, 1), some (10, 1), none, some (20, 0), some (3, 0), some (6, 1), some (16, 0), some (2, 1), some (24, 1), none, some (8, 0), some (4, 0), some (13, 1), some (19, 0), some (23, 1), some (11, 1), none, some (13, 0), some (11, 0), some (20, 1), some (5, 0), some (5, 1), some (3, 1), none, some (15, 0), some (18, 0), some (22, 1), some (9, 0), some (16, 1), some (17, 1), none, some (6, 0), some (24, 0), some (15, 1), some (23, 0), some (12, 1), some (18, 1), none, some (22, 0), some (17, 0), some (8, 1), some (12, 0), some (9, 1), some (4, 1)]

def squareGenerators49 : Fin 1 → ℕ := ![3]

def squareAmplitude49 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 2 else 41)

theorem squareCover49 : SquareWordCover 49 squareGenerators49 squareWords49 := by
  decide +kernel

theorem squareCertificates49 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 49, tableValue 49 (squareValues squareWords49 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 49 (squareValues squareWords49 signs)
        49 (squareAmplitude49 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_49_original_region (chi : DirichletCharacter ℂ 49)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 49 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators49 (by decide +kernel)
    squareWords49 squareCover49 (m := 49) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates49 signs).imp_right fun h => ⟨squareAmplitude49 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
