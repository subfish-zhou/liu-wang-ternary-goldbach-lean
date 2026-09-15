import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 65 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words65 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), none, some (1, 3), some (6, 1), some (2, 1), some (3, 0), none, some (11, 3), some (2, 2), none, some (12, 0), none, some (4, 0), some (7, 2), some (3, 1), some (12, 3), none, some (6, 3), some (17, 2), some (21, 2), some (2, 3), none, none, some (3, 2), some (12, 1), some (17, 0), none, some (4, 3), some (4, 1), some (7, 1), some (7, 3), none, some (6, 0), some (21, 1), some (11, 2), none, none, some (16, 3), some (12, 2), some (6, 2), some (17, 3), none, some (21, 3), some (11, 1), some (4, 2), some (7, 0), none, some (21, 0), none, some (16, 2), some (3, 3), none, some (11, 0), some (16, 1), some (17, 1), some (8, 3), none, some (16, 0), some (8, 2), some (8, 1), some (8, 0)]
def generators65 : Fin 2 → ℕ := ![2, 3]
def amplitude65 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 3) else (if signs 1 then 4 else 47))

theorem cover65 : SquareWordCover 65 generators65 words65 := by decide +kernel

theorem certificates65 : ∀ signs : Fin 2 → Bool,
    periodSum 65 (squareValues words65 signs) ≠ 0 ∨
      Weighted 65 (squareValues words65 signs) 65 (amplitude65 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level65 (chi : DirichletCharacter ℂ 65) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 65 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators65 (by decide +kernel)
    words65 cover65 (m := 65) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates65 signs).imp_right fun h => ⟨amplitude65 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
