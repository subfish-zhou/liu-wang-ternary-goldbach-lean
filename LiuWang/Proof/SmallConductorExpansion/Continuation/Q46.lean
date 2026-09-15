import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 46, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords46 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (7, 0), none, some (1, 1), none, some (11, 1), none, some (3, 0), none, some (19, 1), none, some (17, 0), none, some (7, 1), none, some (13, 1), none, some (17, 1), none, some (15, 1), none, none, none, some (5, 0), none, some (21, 0), none, some (11, 0), none, some (13, 0), none, some (5, 1), none, some (9, 0), none, some (9, 1), none, some (19, 0), none, some (15, 0), none, some (21, 1), none, some (3, 1)]

def squareGenerators46 : Fin 1 → ℕ := ![5]

def squareAmplitude46 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 3 else 21)

theorem squareCover46 : SquareWordCover 46 squareGenerators46 squareWords46 := by
  decide +kernel

theorem squareCertificates46 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 46, tableValue 46 (squareValues squareWords46 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 46 (squareValues squareWords46 signs)
        46 (squareAmplitude46 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_46_original_region (chi : DirichletCharacter ℂ 46)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 46 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators46 (by decide +kernel)
    squareWords46 squareCover46 (m := 46) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates46 signs).imp_right fun h => ⟨squareAmplitude46 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
