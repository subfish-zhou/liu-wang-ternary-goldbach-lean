import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 60, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords60 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, none, none, some (1, 1), none, none, none, some (1, 2), none, some (1, 4), none, none, none, some (1, 3), none, some (7, 5), none, none, none, some (1, 6), none, none, none, none, none, some (7, 7), none, some (1, 5), none, none, none, none, none, some (7, 4), none, none, none, some (1, 7), none, some (7, 1), none, none, none, some (7, 6), none, some (7, 0), none, none, none, some (7, 3), none, none, none, none, none, some (7, 2)]

def squareGenerators60 : Fin 3 → ℕ := ![7, 11, 13]

def squareAmplitude60 (signs : Fin 3 → Bool) : ℚ := (if signs 0 then (if signs 1 then (if signs 2 then 2 else 1) else (if signs 2 then 1 else 2)) else (if signs 1 then (if signs 2 then 2 else 2) else (if signs 2 then 3 else 15)))

theorem squareCover60 : SquareWordCover 60 squareGenerators60 squareWords60 := by
  decide +kernel

theorem squareCertificates60 : ∀ signs : Fin 3 → Bool,
    (∑ k ∈ range 60, tableValue 60 (squareValues squareWords60 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 60 (squareValues squareWords60 signs)
        60 (squareAmplitude60 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_60_original_region (chi : DirichletCharacter ℂ 60)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 60 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators60 (by decide +kernel)
    squareWords60 squareCover60 (m := 60) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates60 signs).imp_right fun h => ⟨squareAmplitude60 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
