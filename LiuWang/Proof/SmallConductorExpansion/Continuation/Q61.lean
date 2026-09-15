import LiuWang.Proof.SmallConductorExpansion.Continuation.SquareWords

/-! # All quadratic characters at level 61, via exhaustive square cosets -/

set_option autoImplicit false
noncomputable section

open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def squareWords61 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (8, 0), some (2, 0), some (26, 0), some (8, 1), some (20, 1), some (2, 1), some (3, 0), some (26, 1), some (6, 1), some (16, 0), some (14, 0), some (21, 0), some (25, 0), some (4, 0), some (10, 1), some (3, 1), some (18, 0), some (9, 0), some (23, 1), some (12, 0), some (15, 1), some (16, 1), some (5, 0), some (14, 1), some (24, 0), some (21, 1), some (17, 1), some (25, 1), some (30, 1), some (4, 1), some (13, 1), some (20, 0), some (29, 1), some (6, 0), some (7, 1), some (18, 1), some (10, 0), some (9, 1), some (23, 0), some (15, 0), some (28, 1), some (12, 1), some (17, 0), some (30, 0), some (13, 0), some (29, 0), some (7, 0), some (5, 1), some (19, 1), some (28, 0), some (22, 1), some (24, 1), some (27, 1), some (19, 0), some (22, 0), some (27, 0), some (11, 1), some (11, 0)]

def squareGenerators61 : Fin 1 → ℕ := ![2]

def squareAmplitude61 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 4 else 59)

theorem squareCover61 : SquareWordCover 61 squareGenerators61 squareWords61 := by
  decide +kernel

theorem squareCertificates61 : ∀ signs : Fin 1 → Bool,
    (∑ k ∈ range 61, tableValue 61 (squareValues squareWords61 signs) k) ≠ 0 ∨
      RationalWeightedCertificate 61 (squareValues squareWords61 signs)
        61 (squareAmplitude61 signs) (511 / 500) := by
  unfold RationalWeightedCertificate
  decide +kernel

theorem quadratic_61_original_region (chi : DirichletCharacter ℂ 61)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 61 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_original_region chi hc hsq squareGenerators61 (by decide +kernel)
    squareWords61 squareCover61 (m := 61) (by decide) (by decide)
    (n := 32) (by decide) (A := 511 / 500) (by norm_num) (by norm_num) _
    (log_scale_thirtytwo (by linarith)) hb
  intro signs
  exact (squareCertificates61 signs).imp_right fun h => ⟨squareAmplitude61 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation
