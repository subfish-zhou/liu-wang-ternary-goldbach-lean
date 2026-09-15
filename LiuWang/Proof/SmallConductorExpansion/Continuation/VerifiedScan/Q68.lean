import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 68 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words68 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (5, 1), none, some (3, 0), none, some (7, 1), none, some (9, 0), none, some (1, 3), none, none, none, some (13, 3), none, some (15, 0), none, some (11, 1), none, some (5, 0), none, some (3, 1), none, some (13, 2), none, some (13, 1), none, some (13, 0), none, some (5, 3), none, some (15, 2), none, some (9, 1), none, some (7, 2), none, some (15, 3), none, some (3, 2), none, some (11, 3), none, some (7, 0), none, none, none, some (11, 0), none, some (7, 3), none, some (5, 2), none, some (9, 3), none, some (11, 2), none, some (15, 1), none, some (9, 2), none, some (3, 3)]
def generators68 : Fin 2 → ℕ := ![3, 5]
def amplitude68 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 1) else (if signs 1 then 8 else 31))

theorem cover68 : SquareWordCover 68 generators68 words68 := by decide +kernel

theorem certificates68 : ∀ signs : Fin 2 → Bool,
    periodSum 68 (squareValues words68 signs) ≠ 0 ∨
      Weighted 68 (squareValues words68 signs) 68 (amplitude68 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level68 (chi : DirichletCharacter ℂ 68) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 68 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators68 (by decide +kernel)
    words68 cover68 (m := 68) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates68 signs).imp_right fun h => ⟨amplitude68 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
