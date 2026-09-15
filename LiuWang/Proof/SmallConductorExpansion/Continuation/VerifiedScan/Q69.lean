import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 69 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words69 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, some (7, 3), some (2, 1), none, some (1, 3), some (4, 2), none, some (17, 0), some (14, 2), none, some (4, 0), some (10, 2), none, some (8, 3), some (2, 2), none, some (4, 3), none, none, some (5, 0), some (17, 1), none, some (14, 3), some (7, 1), none, some (10, 0), some (4, 1), none, some (10, 3), some (11, 1), none, some (11, 3), some (7, 2), none, some (2, 3), some (20, 1), none, some (5, 3), some (8, 2), none, none, some (14, 1), none, some (7, 0), some (5, 1), none, some (11, 0), some (11, 2), none, some (20, 0), some (5, 2), none, some (14, 0), some (8, 1), none, some (17, 3), some (10, 1), none, some (8, 0), some (17, 2), none, some (20, 3), some (20, 2)]
def generators69 : Fin 2 → ℕ := ![2, 5]
def amplitude69 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 4) else (if signs 1 then 3 else 43))

theorem cover69 : SquareWordCover 69 generators69 words69 := by decide +kernel

theorem certificates69 : ∀ signs : Fin 2 → Bool,
    periodSum 69 (squareValues words69 signs) ≠ 0 ∨
      Weighted 69 (squareValues words69 signs) 69 (amplitude69 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level69 (chi : DirichletCharacter ℂ 69) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 69 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators69 (by decide +kernel)
    words69 cover69 (m := 69) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates69 signs).imp_right fun h => ⟨amplitude69 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
