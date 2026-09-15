import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 66 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words66 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, none, none, some (7, 2), none, none, none, some (5, 3), none, some (19, 2), none, none, none, some (19, 1), none, some (5, 0), none, none, none, some (19, 3), none, some (19, 0), none, none, none, some (1, 3), none, some (13, 0), none, none, none, some (13, 3), none, some (5, 2), none, none, none, some (7, 1), none, some (7, 0), none, none, none, some (13, 1), none, none, none, none, none, some (5, 1), none, some (13, 2), none, none, none, some (7, 3)]
def generators66 : Fin 2 → ℕ := ![5, 7]
def amplitude66 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 3 else 2) else (if signs 1 then 2 else 19))

theorem cover66 : SquareWordCover 66 generators66 words66 := by decide +kernel

theorem certificates66 : ∀ signs : Fin 2 → Bool,
    periodSum 66 (squareValues words66 signs) ≠ 0 ∨
      Weighted 66 (squareValues words66 signs) 66 (amplitude66 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level66 (chi : DirichletCharacter ℂ 66) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 66 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators66 (by decide +kernel)
    words66 cover66 (m := 66) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates66 signs).imp_right fun h => ⟨amplitude66 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
