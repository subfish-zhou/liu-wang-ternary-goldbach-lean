import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 80 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words80 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, none, none, some (1, 2), none, some (3, 0), none, some (1, 4), none, some (7, 6), none, none, none, some (7, 5), none, some (3, 4), none, some (1, 3), none, some (7, 2), none, none, none, some (3, 1), none, some (3, 3), none, some (11, 7), none, some (1, 5), none, none, none, some (11, 6), none, some (7, 7), none, some (11, 0), none, some (11, 1), none, none, none, some (11, 2), none, some (7, 0), none, some (11, 4), none, some (3, 6), none, none, none, some (3, 5), none, some (7, 4), none, some (11, 3), none, some (3, 2), none, none, none, some (7, 1), none, some (7, 3), none, some (1, 7), none, some (11, 5), none, none, none, some (1, 6), none, some (3, 7)]
def generators80 : Fin 3 → ℕ := ![3, 7, 11]
def amplitude80 (signs : Fin 3 → Bool) : ℚ := (if signs 0 then (if signs 1 then (if signs 2 then 1 else 1) else (if signs 2 then 2 else 4)) else (if signs 1 then (if signs 2 then 2 else 4) else (if signs 2 then 4 else 31)))

theorem cover80 : SquareWordCover 80 generators80 words80 := by decide +kernel

theorem certificates80 : ∀ signs : Fin 3 → Bool,
    periodSum 80 (squareValues words80 signs) ≠ 0 ∨
      Weighted 80 (squareValues words80 signs) 80 (amplitude80 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level80 (chi : DirichletCharacter ℂ 80) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 80 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators80 (by decide +kernel)
    words80 cover80 (m := 80) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates80 signs).imp_right fun h => ⟨amplitude80 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
