import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 71 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words71 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (12, 0), some (28, 0), some (2, 0), some (17, 0), some (19, 0), some (1, 1), some (24, 0), some (3, 0), some (9, 0), some (23, 1), some (15, 0), some (15, 1), some (12, 1), some (21, 0), some (4, 0), some (16, 1), some (35, 0), some (27, 0), some (34, 0), some (28, 1), some (8, 1), some (14, 1), some (33, 0), some (5, 0), some (33, 1), some (13, 0), some (2, 1), some (10, 0), some (32, 0), some (20, 1), some (23, 0), some (5, 1), some (21, 1), some (17, 1), some (6, 0), some (26, 0), some (31, 0), some (6, 1), some (18, 0), some (4, 1), some (19, 1), some (16, 0), some (25, 1), some (20, 0), some (26, 1), some (13, 1), some (30, 0), some (7, 0), some (11, 0), some (22, 1), some (30, 1), some (31, 1), some (14, 0), some (35, 1), some (24, 1), some (25, 0), some (22, 0), some (7, 1), some (29, 0), some (10, 1), some (27, 1), some (3, 1), some (8, 0), some (29, 1), some (11, 1), some (18, 1), some (32, 1), some (34, 1), some (9, 1)]
def generators71 : Fin 1 → ℕ := ![7]
def amplitude71 (signs : Fin 1 → Bool) : ℚ := (if signs 0 then 10 else 69)

theorem cover71 : SquareWordCover 71 generators71 words71 := by decide +kernel

theorem certificates71 : ∀ signs : Fin 1 → Bool,
    periodSum 71 (squareValues words71 signs) ≠ 0 ∨
      Weighted 71 (squareValues words71 signs) 71 (amplitude71 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level71 (chi : DirichletCharacter ℂ 71) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 71 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators71 (by decide +kernel)
    words71 cover71 (m := 71) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates71 signs).imp_right fun h => ⟨amplitude71 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
