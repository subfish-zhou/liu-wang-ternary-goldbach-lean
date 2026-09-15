import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

/-! # Verified-scan certificate for every quadratic character at level 78 -/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan

def words78 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, none, none, some (1, 1), none, some (1, 2), none, none, none, some (7, 1), none, none, none, none, none, some (5, 3), none, some (5, 2), none, none, none, some (11, 3), none, some (5, 0), none, none, none, some (23, 3), none, some (7, 2), none, none, none, some (1, 3), none, some (23, 2), none, none, none, some (17, 1), none, some (11, 0), none, none, none, some (5, 1), none, some (7, 0), none, none, none, some (17, 3), none, some (17, 0), none, none, none, some (11, 1), none, some (23, 0), none, none, none, none, none, some (11, 2), none, none, none, some (23, 1), none, some (17, 2), none, none, none, some (7, 3)]
def generators78 : Fin 2 → ℕ := ![5, 7]
def amplitude78 (signs : Fin 2 → Bool) : ℚ := (if signs 0 then (if signs 1 then 2 else 1) else (if signs 1 then 4 else 23))

theorem cover78 : SquareWordCover 78 generators78 words78 := by decide +kernel

theorem certificates78 : ∀ signs : Fin 2 → Bool,
    periodSum 78 (squareValues words78 signs) ≠ 0 ∨
      Weighted 78 (squareValues words78 signs) 78 (amplitude78 signs) (509 / 500) := by
  unfold Weighted
  decide +kernel

theorem level78 (chi : DirichletCharacter ℂ 78) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hx : 78 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply square_word_scan_original_region chi hc hsq generators78 (by decide +kernel)
    words78 cover78 (m := 78) (by decide +kernel) (by decide +kernel)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_dyadic (j := 6) (by norm_num; linarith) (by norm_num)) hb
  intro signs
  exact (certificates78 signs).imp_right fun h => ⟨amplitude78 signs, h⟩

end LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan
