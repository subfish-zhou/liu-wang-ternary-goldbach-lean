import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 42, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords42 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, none, none, none, none, some (1, 2), none, some (1, 3), none, none, none, some (11, 1), none, some (11, 3), none, none, none, some (5, 2), none, some (5, 0), none, none, none, some (11, 2), none, some (5, 3), none, none, none, none, none, some (11, 0), none, none, none, some (5, 1)]

def squareGenerators42 : Fin 2 → ℕ := ![5, 11]

def squareAmplitude42 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 2) else (if signs 1 then 2 else 11))

theorem squareCover42 : SquareWordCover 42 squareGenerators42 squareWords42 := by
  decide +kernel

theorem squareCertificates42 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 42, tableValue 42 (squareValues squareWords42 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 42 (squareValues squareWords42 signs)
        42 (squareAmplitude42 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_42_original_region (chi : DirichletCharacter ℂ 42)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 42 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators42 (by decide +kernel)
    squareWords42 squareCover42 (m := 42) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates42 signs).imp_right fun h => ⟨squareAmplitude42 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
