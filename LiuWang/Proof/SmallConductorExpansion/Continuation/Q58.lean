import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 58, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords58 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (11, 0), none, some (23, 0), none, some (3, 0), none, some (9, 1), none, some (19, 0), none, some (11, 1), none, some (5, 1), none, some (25, 1), none, some (23, 1), none, some (9, 0), none, some (5, 0), none, some (3, 1), none, none, none, some (7, 1), none, some (27, 0), none, some (21, 0), none, some (15, 1), none, some (19, 1), none, some (27, 1), none, some (13, 1), none, some (25, 0), none, some (21, 1), none, some (7, 0), none, some (15, 0), none, some (13, 0), none, some (17, 1), none, some (17, 0)]

def squareGenerators58 : Fin 1 → ℕ := ![3]

def squareAmplitude58 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 3 else 27)

theorem squareCover58 : SquareWordCover 58 squareGenerators58 squareWords58 := by
  decide +kernel

theorem squareCertificates58 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 58, tableValue 58 (squareValues squareWords58 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 58 (squareValues squareWords58 signs)
        58 (squareAmplitude58 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_58_original_region (chi : DirichletCharacter ℂ 58)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 58 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators58 (by decide +kernel)
    squareWords58 squareCover58 (m := 58) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates58 signs).imp_right fun h => ⟨squareAmplitude58 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
