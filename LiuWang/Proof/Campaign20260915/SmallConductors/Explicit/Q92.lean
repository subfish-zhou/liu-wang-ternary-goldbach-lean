import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Explicit

def words92 : List (Option (ℕ × ℕ)) := [none, some (1, 0), none, some (1, 1), none, some (1, 2), none, some (5, 3), none, some (3, 0), none, some (17, 3), none, some (17, 0), none, some (1, 3), none, some (13, 2), none, some (9, 3), none, some (15, 2), none, none, none, some (5, 0), none, some (3, 1), none, some (11, 0), none, some (15, 1), none, some (5, 2), none, some (21, 1), none, some (9, 2), none, some (17, 1), none, some (15, 0), none, some (3, 3), none, some (3, 2), none, some (13, 1), none, some (7, 0), none, some (13, 3), none, some (11, 2), none, some (7, 1), none, some (19, 2), none, some (9, 1), none, some (7, 2), none, some (15, 3), none, some (17, 2), none, some (11, 3), none, none, none, some (19, 1), none, some (21, 0), none, some (5, 1), none, some (13, 0), none, some (19, 3), none, some (9, 0), none, some (21, 3), none, some (19, 0), none, some (11, 1), none, some (21, 2), none, some (7, 3)]

def generators92 : Fin 2 → ℕ := ![3, 5]

theorem cover92 : SquareWordCover 92 generators92 words92 := by
  decide +kernel

theorem certificates92 : ∀ signs : Fin 2 → Bool,
    VerifiedScan.periodSum 92 (squareValues words92 signs) ≠ 0 ∨
      VerifiedScan.Weighted 92 (squareValues words92 signs) 92 20 (509 / 500) := by
  unfold VerifiedScan.Weighted
  decide +kernel

theorem level92 (chi : DirichletCharacter ℂ 92)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 92 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  apply VerifiedScan.square_word_scan_original_region chi hc hsq generators92
    (by decide +kernel) words92 cover92 (m := 92) (by decide) (dvd_refl 92)
    (n := 40) (by decide) (A := 509 / 500) (by norm_num) (by norm_num) _
    (log_scale_forty (by linarith)) hb
  intro signs
  exact (certificates92 signs).imp_right fun h => ⟨20, h⟩

#print axioms level92

end LiuWang.Proof.Campaign20260915.SmallConductors.Explicit
