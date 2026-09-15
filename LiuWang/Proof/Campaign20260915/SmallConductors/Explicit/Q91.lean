import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words91 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), some (4, 3), some (1, 3), none, some (2, 1), some (3, 0), some (8, 2), some (18, 1), some (2, 2), none, none, some (12, 1), some (4, 0), some (6, 2), some (3, 1), some (25, 3), some (8, 3), none, some (29, 0), some (32, 0), some (2, 3), some (5, 0), none, some (3, 2), none, some (22, 0), some (11, 0), some (9, 3), some (4, 1), some (18, 3), some (6, 3), none, some (6, 0), some (8, 1), some (15, 2), none, some (16, 2), some (29, 3), none, some (15, 0), some (29, 1), some (12, 3), some (32, 1), some (32, 3), some (4, 2), none, some (5, 1), some (18, 0), none, some (12, 0), some (3, 3), some (25, 2), none, some (16, 1), some (22, 1), some (5, 3), some (11, 1), some (9, 2), some (18, 2), none, some (8, 0), none, some (29, 2), some (25, 1), some (12, 2), some (32, 2), none, some (9, 1), some (6, 1), some (19, 3), some (16, 0), some (5, 2), some (15, 3), none, none, some (25, 0), some (16, 3), some (9, 0), some (19, 2), some (22, 3), none, some (19, 1), some (15, 1), some (22, 2), some (19, 0), some (11, 3), some (11, 2)]

def generators91 : Fin 2 → ℕ := ![2, 3]

theorem cover91 : SquareWordCover 91 generators91 words91 := by
  decide +kernel

theorem certificates91 : ∀ signs : Fin 2 → Bool,
    VerifiedScan.periodSum 91 (squareValues words91 signs) ≠ 0 ∨
      VerifiedScan.Weighted 91 (squareValues words91 signs) 91 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level91 (chi : DirichletCharacter ℂ 91)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 91 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators91
    (by decide +kernel) words91 cover91 (m := 91) (by decide) (dvd_refl 91)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates91 signs).imp_right fun h => ⟨20, h⟩

#print axioms level91

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
