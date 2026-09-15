import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 75 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words75 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), none, none, some (1, 2), some (2, 1), none, none, some (7, 3), none, some (22, 2), some (1, 3), none, some (4, 0), some (11, 1), none, some (13, 0), none, none, some (11, 2), some (7, 1), none, none, some (22, 3), none, some (2, 2), some (19, 3), none, some (16, 0), some (4, 1), none, some (22, 0), none, none, some (4, 2), some (13, 1), none, none, some (13, 3), none, some (7, 2), some (11, 3), none, some (11, 0), some (19, 1), none, some (7, 0), none, none, some (19, 2), some (8, 1), none, none, some (2, 3), none, some (13, 2), some (16, 3), none, some (19, 0), some (16, 1), none, some (8, 0), none, none, some (16, 2), some (22, 1), none, none, some (8, 3), none, some (8, 2), some (4, 3)]
def generators75 : Fin 2 → ℕ := ![2, 7]
def amplitude75 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 1 else 2) else (if signs 1 then 3 else 39))

theorem cover75 : SquareWordCover 75 generators75 words75 := by decide +kernel

theorem certificates75 : ∀ signs : Fin 2 → Bool,
    periodSum 75 (squareValues words75 signs) ≠ 0 ∨
      Weighted 75 (squareValues words75 signs) 75 (amplitude75 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level75 (chi : DirichletCharacter ℂ 75) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 75 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators75 (by decide +kernel)
    words75 cover75 (m := 75) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates75 signs).imp_right fun h => ⟨amplitude75 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
