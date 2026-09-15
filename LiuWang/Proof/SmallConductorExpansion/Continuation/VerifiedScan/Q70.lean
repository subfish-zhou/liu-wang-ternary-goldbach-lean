import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 70 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words70 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, none, none, none, none, some (3, 0), none, some (9, 0), none, some (11, 1), none, none, none, some (13, 1), none, some (1, 2), none, none, none, some (3, 3), none, none, none, some (3, 1), none, some (13, 0), none, some (3, 2), none, some (9, 1), none, none, none, some (11, 3), none, some (23, 0), none, some (23, 2), none, some (13, 3), none, none, none, some (23, 1), none, none, none, some (11, 0), none, some (23, 3), none, none, none, some (1, 3), none, some (11, 2), none, some (13, 2), none, none, none, none, none, some (9, 3), none, some (9, 2)]
def generators70 : Fin 2 → ℕ := ![3, 19]
def amplitude70 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 2) else (if signs 1 then 6 else 23))

theorem cover70 : SquareWordCover 70 generators70 words70 := by decide +kernel

theorem certificates70 : ∀ signs : Fin 2 → Bool,
    periodSum 70 (squareValues words70 signs) ≠ 0 ∨
      Weighted 70 (squareValues words70 signs) 70 (amplitude70 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level70 (chi : DirichletCharacter ℂ 70) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 70 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators70 (by decide +kernel)
    words70 cover70 (m := 70) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates70 signs).imp_right fun h => ⟨amplitude70 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
