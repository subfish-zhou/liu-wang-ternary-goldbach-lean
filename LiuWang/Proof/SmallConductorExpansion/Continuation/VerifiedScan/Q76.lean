import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 76 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words76 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (9, 0), none, some (1, 2), none, some (3, 0), none, some (11, 2), none, some (15, 3), none, some (9, 1), none, some (13, 0), none, none, none, some (1, 3), none, some (5, 2), none, some (5, 0), none, some (3, 1), none, some (9, 3), none, some (17, 1), none, some (11, 3), none, some (9, 2), none, some (3, 3), none, some (7, 2), none, some (7, 3), none, some (13, 2), none, some (11, 0), none, some (17, 2), none, some (7, 0), none, some (13, 1), none, some (13, 3), none, some (15, 2), none, none, none, some (11, 1), none, some (17, 0), none, some (3, 2), none, some (17, 3), none, some (15, 1), none, some (5, 3), none, some (7, 1), none, some (15, 0), none, some (5, 1)]
def generators76 : Fin 2 → ℕ := ![3, 7]
def amplitude76 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 4) else (if signs 1 then 3 else 35))

theorem cover76 : SquareWordCover 76 generators76 words76 := by decide +kernel

theorem certificates76 : ∀ signs : Fin 2 → Bool,
    periodSum 76 (squareValues words76 signs) ≠ 0 ∨
      Weighted 76 (squareValues words76 signs) 76 (amplitude76 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level76 (chi : DirichletCharacter ℂ 76) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 76 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators76 (by decide +kernel)
    words76 cover76 (m := 76) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates76 signs).imp_right fun h => ⟨amplitude76 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
