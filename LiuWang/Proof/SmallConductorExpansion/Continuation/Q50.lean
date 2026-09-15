import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 50, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords50 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, none, none, some (13, 1), none, some (3, 0), none, some (19, 0), none, some (11, 1), none, none, none, some (17, 1), none, some (13, 0), none, some (11, 0), none, some (21, 1), none, none, none, some (3, 1), none, some (23, 0), none, some (9, 0), none, some (19, 1), none, none, none, some (23, 1), none, some (17, 0), none, some (21, 0), none, some (9, 1), none, none, none, some (7, 1), none, some (7, 0)]

def squareGenerators50 : Fin 1 → ℕ := ![3]

def squareAmplitude50 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 1 else 19)

theorem squareCover50 : SquareWordCover 50 squareGenerators50 squareWords50 := by
  decide +kernel

theorem squareCertificates50 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 50, tableValue 50 (squareValues squareWords50 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 50 (squareValues squareWords50 signs)
        50 (squareAmplitude50 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_50_original_region (chi : DirichletCharacter ℂ 50)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 50 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators50 (by decide +kernel)
    squareWords50 squareCover50 (m := 50) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates50 signs).imp_right fun h => ⟨squareAmplitude50 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
