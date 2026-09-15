import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 72 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words72 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, some (5, 3), none, some (1, 4), none, none, none, some (7, 5), none, some (1, 6), none, none, none, some (1, 7), none, some (5, 0), none, none, none, some (7, 1), none, some (5, 2), none, none, none, some (1, 3), none, some (5, 4), none, none, none, some (5, 5), none, some (5, 6), none, none, none, some (7, 7), none, some (7, 0), none, none, none, some (5, 1), none, some (7, 2), none, none, none, some (7, 3), none, some (7, 4), none, none, none, some (1, 5), none, some (7, 6), none, none, none, some (5, 7)]
def generators72 : Fin 3 → ℕ := ![5, 7, 13]
def amplitude72 (signs : Fin 3 → Bool) : ℚ := (if signs 0 then (if signs 1 then (if signs 2 then 1 else 1) else (if signs 2 then 1 else 1)) else (if signs 1 then (if signs 2 then 2 else 2) else (if signs 2 then 4 else 23)))

theorem cover72 : SquareWordCover 72 generators72 words72 := by decide +kernel

theorem certificates72 : ∀ signs : Fin 3 → Bool,
    periodSum 72 (squareValues words72 signs) ≠ 0 ∨
      Weighted 72 (squareValues words72 signs) 72 (amplitude72 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level72 (chi : DirichletCharacter ℂ 72) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 72 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators72 (by decide +kernel)
    words72 cover72 (m := 72) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates72 signs).imp_right fun h => ⟨amplitude72 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
