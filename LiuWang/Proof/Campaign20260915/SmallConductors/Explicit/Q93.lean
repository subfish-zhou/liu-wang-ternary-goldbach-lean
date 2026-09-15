import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words93 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (7, 1), none, some (10, 0), some (2, 1), none, some (14, 0), some (1, 2), none, some (8, 3), some (10, 1), none, some (4, 0), some (14, 2), none, some (22, 0), some (14, 1), none, some (1, 3), some (22, 2), none, some (5, 0), some (16, 2), none, some (11, 0), some (11, 2), none, none, some (4, 1), none, some (14, 3), some (8, 1), none, some (19, 3), some (22, 1), none, some (28, 0), some (25, 1), none, some (28, 3), some (2, 2), none, some (22, 3), some (16, 1), none, some (7, 0), some (5, 1), none, some (16, 3), some (8, 2), none, some (7, 3), some (11, 1), none, some (11, 3), some (13, 1), none, some (10, 3), none, none, some (8, 0), some (19, 2), none, some (25, 0), some (28, 2), none, some (16, 0), some (19, 1), none, some (4, 3), some (7, 2), none, some (13, 0), some (10, 2), none, some (25, 3), some (28, 1), none, some (19, 0), some (4, 2), none, some (5, 3), some (25, 2), none, some (2, 3), some (5, 2), none, some (13, 3), some (13, 2)]

def generators93 : Fin 2 → ℕ := ![2, 11]

theorem cover93 : SquareWordCover 93 generators93 words93 := by
  decide +kernel

theorem certificates93 : ∀ signs : Fin 2 → Bool,
    VerifiedScan.periodSum 93 (squareValues words93 signs) ≠ 0 ∨
      VerifiedScan.Weighted 93 (squareValues words93 signs) 93 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level93 (chi : DirichletCharacter ℂ 93)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 93 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators93
    (by decide +kernel) words93 cover93 (m := 93) (by decide) (dvd_refl 93)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates93 signs).imp_right fun h => ⟨20, h⟩

#print axioms level93

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
