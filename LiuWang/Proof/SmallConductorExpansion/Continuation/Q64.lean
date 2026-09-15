import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 64, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords64 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (3, 3), none, some (3, 0), none, some (5, 1), none, some (13, 2), none, some (1, 3), none, some (9, 0), none, some (7, 1), none, some (9, 2), none, some (11, 3), none, some (5, 0), none, some (3, 1), none, some (11, 2), none, some (7, 3), none, some (15, 0), none, some (15, 1), none, some (15, 2), none, some (13, 3), none, some (13, 0), none, some (11, 1), none, some (3, 2), none, some (15, 3), none, some (7, 0), none, some (9, 1), none, some (7, 2), none, some (5, 3), none, some (11, 0), none, some (13, 1), none, some (5, 2), none, some (9, 3)]

def squareGenerators64 : Fin 2 → ℕ := ![3, 5]

def squareAmplitude64 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 1) else (if signs 1 then 2 else 31))

theorem squareCover64 : SquareWordCover 64 squareGenerators64 squareWords64 := by
  decide +kernel

theorem squareCertificates64 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 64, tableValue 64 (squareValues squareWords64 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 64 (squareValues squareWords64 signs)
        64 (squareAmplitude64 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_64_original_region (chi : DirichletCharacter ℂ 64)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 64 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators64 (by decide +kernel)
    squareWords64 squareCover64 (m := 64) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates64 signs).imp_right fun h => ⟨squareAmplitude64 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
