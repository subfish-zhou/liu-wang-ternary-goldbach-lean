import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 38, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords38 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (9, 0), none, some (11, 0), none, some (3, 0), none, some (7, 0), none, some (13, 1), none, some (9, 1), none, some (13, 0), none, none, none, some (11, 1), none, some (17, 0), none, some (5, 0), none, some (3, 1), none, some (15, 1), none, some (17, 1), none, some (7, 1), none, some (15, 0), none, some (5, 1)]

def squareGenerators38 : Fin 1 → ℕ := ![3]

def squareAmplitude38 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 4 else 17)

theorem squareCover38 : SquareWordCover 38 squareGenerators38 squareWords38 := by
  decide +kernel

theorem squareCertificates38 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 38, tableValue 38 (squareValues squareWords38 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 38 (squareValues squareWords38 signs)
        38 (squareAmplitude38 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_38_original_region (chi : DirichletCharacter ℂ 38)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 38 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators38 (by decide +kernel)
    squareWords38 squareCover38 (m := 38) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates38 signs).imp_right fun h => ⟨squareAmplitude38 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
