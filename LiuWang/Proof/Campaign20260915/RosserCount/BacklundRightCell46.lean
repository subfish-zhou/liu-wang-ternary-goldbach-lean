import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell46Q : ℕ → ℚ
  | 2 => 503 / 400
  | 3 => 19931 / 10000
  | 4 => 503 / 200
  | 5 => 14599 / 5000
  | 6 => 16253 / 5000
  | 7 => 17651 / 5000
  | 8 => 1509 / 400
  | 9 => 19931 / 5000
  | 10 => 41773 / 10000
  | 11 => 21751 / 5000
  | 12 => 45081 / 10000
  | 13 => 46533 / 10000
  | 14 => 47877 / 10000
  | 15 => 49129 / 10000
  | 16 => 503 / 100
  | _ => 0

private def rightCell46U : ℕ → ℚ
  | 1 => 1
  | 2 => 56873 / 200000
  | 3 => 136273 / 1000000
  | 4 => 80863 / 1000000
  | 5 => 10789 / 200000
  | 6 => 38751 / 1000000
  | 7 => 293 / 10000
  | 8 => 4599 / 200000
  | 9 => 18571 / 1000000
  | 10 => 767 / 50000
  | 11 => 2581 / 200000
  | 12 => 551 / 50000
  | 13 => 9531 / 1000000
  | 14 => 2083 / 250000
  | 15 => 919 / 125000
  | 16 => 6539 / 1000000
  | _ => 0

theorem backlund_right_cell46_scalar :
    Real.log (backlundDirichletEnvelope 16 (9071 / 5000 : ℝ)) ≤ 6231 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 9071 / 5000) (l := 6231 / 10000) (v := 1864579 / 1000000)
    (qt := 11287 / 5000) (ut := 128497 / 1000000) rightCell46Q rightCell46U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell46Q, rightCell46U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell46U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell46 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 46 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      6231 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 46) (a := 9071 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (9071 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell46_scalar

#print axioms backlund_right_cell46_scalar
#print axioms backlund_right_cell46

end LiuWang.Proof.Campaign20260915.RosserCount
