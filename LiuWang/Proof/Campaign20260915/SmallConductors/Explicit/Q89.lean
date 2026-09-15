import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words89 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (25, 0), some (1, 1), some (2, 0), some (19, 0), some (25, 1), some (11, 1), some (39, 0), some (3, 0), some (30, 0), some (10, 0), some (2, 1), some (37, 1), some (8, 1), some (19, 1), some (4, 0), some (27, 0), some (14, 0), some (6, 1), some (38, 0), some (33, 0), some (17, 0), some (44, 1), some (39, 1), some (5, 0), some (35, 1), some (3, 1), some (22, 1), some (43, 1), some (30, 1), some (29, 1), some (11, 0), some (10, 1), some (37, 0), some (31, 1), some (6, 0), some (24, 1), some (28, 1), some (22, 0), some (29, 0), some (42, 1), some (24, 0), some (20, 1), some (20, 0), some (32, 0), some (32, 1), some (15, 0), some (4, 1), some (7, 0), some (36, 0), some (27, 1), some (15, 1), some (26, 0), some (14, 1), some (12, 0), some (16, 1), some (18, 0), some (7, 1), some (41, 1), some (38, 1), some (36, 1), some (13, 1), some (33, 1), some (8, 0), some (9, 1), some (17, 1), some (44, 0), some (35, 0), some (43, 0), some (26, 1), some (31, 0), some (28, 0), some (42, 0), some (23, 1), some (5, 1), some (12, 1), some (21, 1), some (16, 0), some (41, 0), some (13, 0), some (9, 0), some (18, 1), some (40, 1), some (23, 0), some (21, 0), some (34, 1), some (40, 0), some (34, 0)]

def generators89 : Fin 1 → ℕ := ![3]

theorem cover89 : SquareWordCover 89 generators89 words89 := by
  decide +kernel

theorem certificates89 : ∀ signs : Fin 1 → Bool,
    VerifiedScan.periodSum 89 (squareValues words89 signs) ≠ 0 ∨
      VerifiedScan.Weighted 89 (squareValues words89 signs) 89 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level89 (chi : DirichletCharacter ℂ 89)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 89 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators89
    (by decide +kernel) words89 cover89 (m := 89) (by decide) (dvd_refl 89)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates89 signs).imp_right fun h => ⟨20, h⟩

#print axioms level89

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
