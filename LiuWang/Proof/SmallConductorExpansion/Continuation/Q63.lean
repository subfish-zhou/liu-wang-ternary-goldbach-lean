import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 63, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords63 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, none, some (2, 1), none, some (1, 3), some (10, 1), none, some (11, 3), none, none, some (4, 0), some (4, 2), none, some (19, 3), some (2, 2), none, some (20, 0), some (13, 1), none, some (5, 0), some (13, 2), none, none, some (19, 1), none, some (20, 3), some (4, 1), none, some (4, 3), none, none, some (10, 0), some (11, 2), none, some (2, 3), some (19, 2), none, some (13, 0), some (20, 1), none, some (19, 0), some (20, 2), none, none, some (5, 1), none, some (13, 3), some (11, 1), none, some (10, 3), none, none, some (11, 0), some (10, 2), none, some (5, 3), some (5, 2)]

def squareGenerators63 : Fin 2 → ℕ := ![2, 5]

def squareAmplitude63 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 2) else (if signs 1 then 3 else 35))

theorem squareCover63 : SquareWordCover 63 squareGenerators63 squareWords63 := by
  decide +kernel

theorem squareCertificates63 : ∀ signs : Fin 2 → Bool,
    (∑ k ∈ range 63, tableValue 63 (squareValues squareWords63 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 63 (squareValues squareWords63 signs)
        63 (squareAmplitude63 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_63_original_region (chi : DirichletCharacter ℂ 63)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 63 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators63 (by decide +kernel)
    squareWords63 squareCover63 (m := 63) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates63 signs).imp_right fun h => ⟨squareAmplitude63 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
