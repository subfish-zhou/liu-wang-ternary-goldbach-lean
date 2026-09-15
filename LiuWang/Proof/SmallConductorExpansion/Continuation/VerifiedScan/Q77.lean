import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 77 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words77 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (19, 2), some (1, 3), none, some (2, 1), some (3, 0), some (19, 3), none, some (2, 2), some (13, 3), none, some (13, 0), some (4, 0), some (12, 3), some (3, 1), some (4, 3), some (17, 2), none, none, some (10, 0), some (2, 3), some (5, 0), some (26, 2), some (3, 2), none, some (19, 1), some (13, 1), some (6, 2), some (4, 1), none, some (24, 2), none, some (6, 0), some (24, 0), some (8, 2), some (17, 1), some (17, 3), some (15, 3), none, some (26, 1), none, some (13, 2), some (10, 1), some (12, 2), some (4, 2), none, some (5, 1), some (8, 1), some (26, 3), some (19, 0), some (3, 3), none, none, some (12, 1), some (17, 0), some (15, 2), some (26, 0), some (10, 3), some (6, 3), none, some (8, 0), some (15, 1), none, some (12, 0), some (24, 3), some (10, 2), none, some (15, 0), some (6, 1), some (5, 3), some (24, 1), some (5, 2), some (8, 3)]
def generators77 : Fin 2 → ℕ := ![2, 3]
def amplitude77 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 6 else 6) else (if signs 1 then 2 else 59))

theorem cover77 : SquareWordCover 77 generators77 words77 := by decide +kernel

theorem certificates77 : ∀ signs : Fin 2 → Bool,
    periodSum 77 (squareValues words77 signs) ≠ 0 ∨
      Weighted 77 (squareValues words77 signs) 77 (amplitude77 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level77 (chi : DirichletCharacter ℂ 77) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 77 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators77 (by decide +kernel)
    words77 cover77 (m := 77) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates77 signs).imp_right fun h => ⟨amplitude77 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
