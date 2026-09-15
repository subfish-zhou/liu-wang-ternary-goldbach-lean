import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words95 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (7, 1), some (2, 0), none, some (14, 0), some (1, 2), some (2, 1), some (3, 0), none, some (26, 0), some (14, 1), some (23, 1), some (1, 3), none, some (4, 0), some (4, 2), some (3, 1), none, none, some (7, 3), some (26, 1), some (33, 2), some (28, 0), none, some (11, 0), some (21, 1), some (2, 2), some (6, 3), none, some (3, 3), some (4, 1), some (8, 1), some (4, 3), none, some (6, 0), some (16, 1), none, some (18, 0), none, some (8, 3), some (14, 2), some (13, 2), some (33, 0), none, some (33, 3), some (21, 2), some (28, 1), some (7, 0), none, some (28, 3), some (11, 1), some (13, 1), some (23, 0), none, some (2, 3), none, some (7, 2), some (26, 3), none, some (21, 0), some (6, 2), some (3, 2), some (8, 0), none, some (16, 0), some (9, 1), some (8, 2), some (16, 3), none, some (18, 3), some (6, 1), some (28, 2), some (13, 0), none, none, some (26, 2), some (18, 1), some (11, 3), none, some (9, 0), some (16, 2), some (18, 2), some (14, 3), none, some (13, 3), some (11, 2), some (33, 1), some (9, 3), none, some (23, 3), some (9, 2), some (23, 2), some (21, 3)]

def generators95 : Fin 2 → ℕ := ![2, 7]

theorem cover95 : SquareWordCover 95 generators95 words95 := by
  decide +kernel

theorem certificates95 : ∀ signs : Fin 2 → Bool,
    VerifiedScan.periodSum 95 (squareValues words95 signs) ≠ 0 ∨
      VerifiedScan.Weighted 95 (squareValues words95 signs) 95 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level95 (chi : DirichletCharacter ℂ 95)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 95 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators95
    (by decide +kernel) words95 cover95 (m := 95) (by decide) (dvd_refl 95)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates95 signs).imp_right fun h => ⟨20, h⟩

#print axioms level95

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
