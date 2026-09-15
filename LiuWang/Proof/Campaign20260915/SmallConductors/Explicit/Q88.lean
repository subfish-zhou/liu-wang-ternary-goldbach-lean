import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words88 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (1, 4), none, some (3, 0), none, none, none, some (3, 5), none, some (1, 3), none, some (1, 7), none, some (9, 6), none, some (1, 5), none, some (5, 3), none, some (5, 0), none, some (3, 1), none, some (9, 5), none, some (7, 3), none, none, none, some (1, 6), none, some (5, 2), none, some (9, 4), none, some (7, 7), none, some (7, 6), none, some (3, 2), none, some (3, 3), none, some (7, 0), none, some (3, 6), none, some (9, 2), none, none, none, some (9, 7), none, some (7, 1), none, some (7, 5), none, some (3, 4), none, some (3, 7), none, some (9, 1), none, some (7, 2), none, some (9, 3), none, some (5, 7), none, some (5, 1), none, none, none, some (7, 4), none, some (9, 0), none, some (5, 6), none, some (5, 5), none, some (5, 4)]

def generators88 : Fin 3 → ℕ := ![3, 5, 7]

theorem cover88 : SquareWordCover 88 generators88 words88 := by
  decide +kernel

theorem certificates88 : ∀ signs : Fin 3 → Bool,
    VerifiedScan.periodSum 88 (squareValues words88 signs) ≠ 0 ∨
      VerifiedScan.Weighted 88 (squareValues words88 signs) 88 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level88 (chi : DirichletCharacter ℂ 88)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 88 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators88
    (by decide +kernel) words88 cover88 (m := 88) (by decide) (dvd_refl 88)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates88 signs).imp_right fun h => ⟨20, h⟩

#print axioms level88

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
