import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 48, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords48 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, some (5, 3), none, some (1, 4), none, none, none, some (1, 5), none, some (5, 6), none, none, none, some (1, 7), none, some (5, 0), none, none, none, some (5, 1), none, some (5, 2), none, none, none, some (1, 3), none, some (5, 4), none, none, none, some (5, 5), none, some (1, 6), none, none, none, some (5, 7)]

def squareGenerators48 : Fin 3 → ℕ := ![5, 7, 13]

def squareAmplitude48 (signs : Fin 3 → Bool) : ℚ := (if signs 0 then (if signs 1 then (if signs 2 then 1 else 1) else (if signs 2 then 1 else 1)) else (if signs 1 then (if signs 2 then 2 else 2) else (if signs 2 then 4 else 15)))

theorem squareCover48 : SquareWordCover 48 squareGenerators48 squareWords48 := by
  decide +kernel

theorem squareCertificates48 : ∀ signs : Fin 3 → Bool,
    (∑ k ∈ range 48, tableValue 48 (squareValues squareWords48 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 48 (squareValues squareWords48 signs)
        48 (squareAmplitude48 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_48_original_region (chi : DirichletCharacter ℂ 48)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 48 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators48 (by decide +kernel)
    squareWords48 squareCover48 (m := 48) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates48 signs).imp_right fun h => ⟨squareAmplitude48 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
