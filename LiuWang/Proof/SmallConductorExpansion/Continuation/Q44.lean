import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 44, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords44 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (7, 0), none, some (1, 2), none, some (3, 0), none, none, none, some (3, 3), none, some (7, 1), none, some (7, 3), none, some (3, 2), none, some (1, 3), none, some (9, 1), none, some (5, 0), none, some (3, 1), none, some (9, 3), none, some (5, 1), none, none, none, some (7, 2), none, some (9, 0), none, some (9, 2), none, some (5, 3), none, some (5, 2)]

def squareGenerators44 : Fin 2 → ℕ := ![3, 7]

def squareAmplitude44 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 3) else (if signs 1 then 3 else 19))

theorem squareCover44 : SquareWordCover 44 squareGenerators44 squareWords44 := by
  decide +kernel

theorem squareCertificates44 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 44, tableValue 44 (squareValues squareWords44 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 44 (squareValues squareWords44 signs)
        44 (squareAmplitude44 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_44_original_region (chi : DirichletCharacter ℂ 44)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 44 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators44 (by decide +kernel)
    squareWords44 squareCover44 (m := 44) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates44 signs).imp_right fun h => ⟨squareAmplitude44 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
