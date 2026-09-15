import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 35, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords35 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), none, some (1, 3), none, some (2, 1), some (3, 0), none, some (9, 0), some (2, 2), some (4, 2), none, none, some (4, 0), some (8, 2), some (3, 1), some (3, 3), none, none, some (9, 1), some (8, 1), some (2, 3), none, some (4, 3), some (3, 2), none, some (8, 0), none, some (9, 3), some (4, 1), some (9, 2), some (8, 3)]

def squareGenerators35 : Fin 2 → ℕ := ![2, 3]

def squareAmplitude35 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 6) else (if signs 1 then 4 else 23))

theorem squareCover35 : SquareWordCover 35 squareGenerators35 squareWords35 := by
  decide +kernel

theorem squareCertificates35 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 35, tableValue 35 (squareValues squareWords35 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 35 (squareValues squareWords35 signs)
        35 (squareAmplitude35 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_35_original_region (chi : DirichletCharacter ℂ 35)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 35 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators35 (by decide +kernel)
    squareWords35 squareCover35 (m := 35) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates35 signs).imp_right fun h => ⟨squareAmplitude35 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
