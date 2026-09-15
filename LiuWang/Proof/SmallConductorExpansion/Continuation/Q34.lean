import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 34, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords34 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (9, 1), none, some (5, 1), none, some (3, 0), none, some (7, 1), none, some (9, 0), none, some (7, 0), none, none, none, some (11, 0), none, some (15, 0), none, some (11, 1), none, some (5, 0), none, some (3, 1), none, some (15, 1), none, some (13, 1), none, some (13, 0)]

def squareGenerators34 : Fin 1 → ℕ := ![3]

def squareAmplitude34 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 2 else 15)

theorem squareCover34 : SquareWordCover 34 squareGenerators34 squareWords34 := by
  decide +kernel

theorem squareCertificates34 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 34, tableValue 34 (squareValues squareWords34 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 34 (squareValues squareWords34 signs)
        34 (squareAmplitude34 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_34_original_region (chi : DirichletCharacter ℂ 34)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 34 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators34 (by decide +kernel)
    squareWords34 squareCover34 (m := 34) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates34 signs).imp_right fun h => ⟨squareAmplitude34 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
