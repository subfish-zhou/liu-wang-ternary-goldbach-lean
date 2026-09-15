import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words87 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), none, some (2, 0), some (1, 2), none, some (23, 0), some (2, 1), none, some (1, 3), some (7, 1), none, some (10, 0), some (23, 1), none, some (4, 0), some (20, 1), none, some (17, 3), some (2, 2), none, some (14, 0), some (14, 2), none, some (5, 0), some (10, 1), none, some (17, 0), none, none, some (8, 3), some (4, 1), none, some (11, 0), some (23, 2), none, some (13, 3), some (5, 2), none, some (2, 3), some (8, 1), none, some (10, 3), some (14, 1), none, some (14, 3), some (26, 1), none, some (7, 0), some (5, 1), none, some (20, 0), some (17, 2), none, some (7, 3), some (17, 1), none, none, some (8, 2), none, some (26, 3), some (13, 2), none, some (8, 0), some (10, 2), none, some (26, 0), some (11, 1), none, some (23, 3), some (7, 2), none, some (4, 3), some (26, 2), none, some (5, 3), some (13, 1), none, some (11, 3), some (4, 2), none, some (13, 0), some (11, 2), none, some (20, 3), some (20, 2)]

def generators87 : Fin 2 → ℕ := ![2, 5]

theorem cover87 : SquareWordCover 87 generators87 words87 := by
  decide +kernel

theorem certificates87 : ∀ signs : Fin 2 → Bool,
    VerifiedScan.periodSum 87 (squareValues words87 signs) ≠ 0 ∨
      VerifiedScan.Weighted 87 (squareValues words87 signs) 87 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level87 (chi : DirichletCharacter ℂ 87)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 87 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators87
    (by decide +kernel) words87 cover87 (m := 87) (by decide) (dvd_refl 87)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates87 signs).imp_right fun h => ⟨20, h⟩

#print axioms level87

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
