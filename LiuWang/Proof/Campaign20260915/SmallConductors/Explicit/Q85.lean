import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words85 : List (Option (ℕ × ℕ)) := [none, some (1, 0), some (1, 1), some (1, 2), some (2, 0), none, some (1, 3), some (12, 2), some (2, 1), some (3, 0), none, some (4, 3), some (2, 2), some (7, 1), some (12, 3), none, some (4, 0), none, some (3, 1), some (23, 0), none, some (19, 0), some (8, 2), some (6, 2), some (2, 3), none, some (14, 0), some (3, 2), some (24, 2), some (23, 3), none, some (29, 3), some (4, 1), some (12, 1), none, none, some (6, 0), some (18, 2), some (23, 1), some (7, 3), none, some (19, 3), some (19, 1), some (8, 1), some (8, 3), none, some (6, 3), some (24, 1), some (4, 2), some (7, 0), none, none, some (14, 1), some (18, 1), some (3, 3), none, some (24, 3), some (23, 2), some (29, 2), some (12, 0), none, some (9, 3), some (7, 2), some (19, 2), some (8, 0), none, some (24, 0), some (29, 1), none, some (18, 0), none, some (14, 3), some (6, 1), some (9, 2), some (18, 3), none, some (29, 0), some (9, 1), some (14, 2), some (13, 3), none, some (9, 0), some (13, 2), some (13, 1), some (13, 0)]

def generators85 : Fin 2 → ℕ := ![2, 3]

theorem cover85 : SquareWordCover 85 generators85 words85 := by
  decide +kernel

theorem certificates85 : ∀ signs : Fin 2 → Bool,
    VerifiedScan.periodSum 85 (squareValues words85 signs) ≠ 0 ∨
      VerifiedScan.Weighted 85 (squareValues words85 signs) 85 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level85 (chi : DirichletCharacter ℂ 85)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 85 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators85
    (by decide +kernel) words85 cover85 (m := 85) (by decide) (dvd_refl 85)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates85 signs).imp_right fun h => ⟨20, h⟩

#print axioms level85

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
