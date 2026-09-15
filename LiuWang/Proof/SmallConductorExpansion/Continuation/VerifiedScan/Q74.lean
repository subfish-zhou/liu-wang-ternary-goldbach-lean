import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 74 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words74 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (15, 0), none, some (1, 1), none, some (9, 0), none, some (3, 0), none, some (23, 0), none, some (11, 1), none, some (15, 1), none, some (25, 1), none, some (27, 1), none, some (13, 0), none, some (7, 1), none, some (5, 0), none, some (29, 0), none, some (19, 1), none, some (13, 1), none, some (25, 0), none, some (9, 1), none, none, none, some (17, 1), none, some (35, 0), none, some (33, 1), none, some (3, 1), none, some (11, 0), none, some (7, 0), none, some (5, 1), none, some (33, 0), none, some (23, 1), none, some (35, 1), none, some (21, 1), none, some (29, 1), none, some (27, 0), none, some (19, 0), none, some (17, 0), none, some (31, 1), none, some (21, 0), none, some (31, 0)]
def generators74 : Fin 1 → ℕ := ![5]
def amplitude74 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 4 else 35)

theorem cover74 : SquareWordCover 74 generators74 words74 := by decide +kernel

theorem certificates74 : ∀ signs : Fin 1 → Bool,
    periodSum 74 (squareValues words74 signs) ≠ 0 ∨
      Weighted 74 (squareValues words74 signs) 74 (amplitude74 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level74 (chi : DirichletCharacter ℂ 74) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 74 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators74 (by decide +kernel)
    words74 cover74 (m := 74) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates74 signs).imp_right fun h => ⟨amplitude74 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
