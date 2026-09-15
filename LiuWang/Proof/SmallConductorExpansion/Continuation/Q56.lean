import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 56, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords56 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, none, none, some (3, 0), none, some (1, 4), none, some (5, 2), none, some (1, 3), none, some (3, 5), none, some (5, 1), none, none, none, some (3, 3), none, some (5, 0), none, some (3, 1), none, some (3, 7), none, some (5, 6), none, some (1, 5), none, none, none, some (5, 7), none, some (5, 3), none, some (5, 5), none, some (3, 4), none, some (3, 2), none, some (3, 6), none, none, none, some (5, 4), none, some (1, 7), none, some (1, 6)]

def squareGenerators56 : Fin 3 → ℕ := ![3, 5, 11]

def squareAmplitude56 (signs : Fin 3 → Bool) : ℚ := (if signs 0 then (if signs 1 then (if signs 2 then 2 else 1) else (if signs 2 then 2 else 4)) else (if signs 1 then (if signs 2 then 2 else 4) else (if signs 2 then 8 else 23)))

theorem squareCover56 : SquareWordCover 56 squareGenerators56 squareWords56 := by
  decide +kernel

theorem squareCertificates56 : ∀ signs : Fin 3 → Bool,
    (∑ k ∈ range 56, tableValue 56 (squareValues squareWords56 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 56 (squareValues squareWords56 signs)
        56 (squareAmplitude56 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_56_original_region (chi : DirichletCharacter ℂ 56)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 56 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators56 (by decide +kernel)
    squareWords56 squareCover56 (m := 56) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates56 signs).imp_right fun h => ⟨squareAmplitude56 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
