import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words97 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (14, 0), some (10, 0), some (2, 0), some (1, 1), some (43, 0), some (46, 1), some (28, 0), some (3, 0), some (14, 1), some (37, 0), some (20, 0), some (33, 1), some (35, 1), some (10, 1), some (4, 0), some (9, 1), some (42, 0), some (16, 1), some (2, 1), some (25, 1), some (33, 0), some (11, 1), some (11, 0), some (5, 0), some (23, 1), some (30, 0), some (5, 1), some (8, 1), some (43, 1), some (15, 0), some (41, 0), some (18, 0), some (29, 1), some (36, 0), some (6, 0), some (45, 1), some (30, 1), some (39, 1), some (28, 1), some (12, 1), some (38, 1), some (25, 0), some (23, 0), some (3, 1), some (40, 1), some (12, 0), some (40, 0), some (7, 0), some (27, 0), some (7, 1), some (31, 1), some (21, 0), some (32, 0), some (37, 1), some (27, 1), some (34, 1), some (15, 1), some (19, 1), some (20, 1), some (35, 0), some (16, 0), some (41, 1), some (8, 0), some (29, 0), some (39, 0), some (24, 1), some (18, 1), some (13, 1), some (19, 0), some (21, 1), some (13, 0), some (48, 0), some (48, 1), some (47, 0), some (32, 1), some (44, 1), some (36, 1), some (46, 0), some (4, 1), some (9, 0), some (26, 1), some (6, 1), some (47, 1), some (45, 0), some (38, 0), some (17, 1), some (31, 0), some (34, 0), some (42, 1), some (24, 0), some (22, 1), some (44, 0), some (26, 0), some (17, 0), some (22, 0)]

def generators97 : Fin 1 → ℕ := ![5]

theorem cover97 : SquareWordCover 97 generators97 words97 := by
  decide +kernel

theorem certificates97 : ∀ signs : Fin 1 → Bool,
    VerifiedScan.periodSum 97 (squareValues words97 signs) ≠ 0 ∨
      VerifiedScan.Weighted 97 (squareValues words97 signs) 97 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level97 (chi : DirichletCharacter ℂ 97)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 97 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators97
    (by decide +kernel) words97 cover97 (m := 97) (by decide) (dvd_refl 97)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates97 signs).imp_right fun h => ⟨20, h⟩

#print axioms level97

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
