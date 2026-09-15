import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 52, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords52 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (7, 3), none, some (3, 0), none, some (5, 3), none, none, none, some (1, 3), none, some (11, 0), none, some (9, 3), none, some (5, 2), none, some (5, 1), none, some (5, 0), none, some (3, 1), none, some (9, 0), none, some (3, 3), none, some (11, 2), none, some (9, 1), none, some (7, 2), none, none, none, some (9, 2), none, some (7, 1), none, some (3, 2), none, some (11, 3), none, some (7, 0), none, some (11, 1)]

def squareGenerators52 : Fin 2 → ℕ := ![3, 5]

def squareAmplitude52 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 5 else 1) else (if signs 1 then 2 else 23))

theorem squareCover52 : SquareWordCover 52 squareGenerators52 squareWords52 := by
  decide +kernel

theorem squareCertificates52 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 52, tableValue 52 (squareValues squareWords52 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 52 (squareValues squareWords52 signs)
        52 (squareAmplitude52 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_52_original_region (chi : DirichletCharacter ℂ 52)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 52 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators52 (by decide +kernel)
    squareWords52 squareCover52 (m := 52) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates52 signs).imp_right fun h => ⟨squareAmplitude52 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
