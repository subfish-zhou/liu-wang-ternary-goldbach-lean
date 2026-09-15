import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 40, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords40 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, none, none, some (1, 2), none, some (3, 0), none, some (1, 4), none, some (3, 6), none, none, none, some (3, 5), none, some (3, 4), none, some (1, 3), none, some (3, 2), none, none, none, some (3, 1), none, some (3, 3), none, some (1, 7), none, some (1, 5), none, none, none, some (1, 6), none, some (3, 7)]

def squareGenerators40 : Fin 3 → ℕ := ![3, 7, 11]

def squareAmplitude40 (signs : Fin 3 → Bool) : ℚ := (if signs 0 then (if signs 1 then (if signs 2 then 1 else 1) else (if signs 2 then 2 else 4)) else (if signs 1 then (if signs 2 then 2 else 4) else (if signs 2 then 4 else 15)))

theorem squareCover40 : SquareWordCover 40 squareGenerators40 squareWords40 := by
  decide +kernel

theorem squareCertificates40 : ∀ signs : Fin 3 → Bool,
    (∑ k ∈ range 40, tableValue 40 (squareValues squareWords40 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 40 (squareValues squareWords40 signs)
        40 (squareAmplitude40 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_40_original_region (chi : DirichletCharacter ℂ 40)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 40 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators40 (by decide +kernel)
    squareWords40 squareCover40 (m := 40) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates40 signs).imp_right fun h => ⟨squareAmplitude40 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
