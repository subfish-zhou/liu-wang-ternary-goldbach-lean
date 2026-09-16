import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell23Q : ℕ → ℚ
  | 2 => 2049 / 1250
  | 3 => 12991 / 5000
  | 4 => 6557 / 2000
  | 5 => 38063 / 10000
  | 6 => 339 / 80
  | 7 => 2301 / 500
  | 8 => 24589 / 5000
  | 9 => 12991 / 2500
  | 10 => 6807 / 1250
  | 11 => 5671 / 1000
  | 12 => 3673 / 625
  | 13 => 60661 / 10000
  | 14 => 62413 / 10000
  | 15 => 12809 / 2000
  | 16 => 65571 / 10000
  | _ => 0

private def rightCell23U : ℕ → ℚ
  | 1 => 1
  | 2 => 24267 / 125000
  | 3 => 9301 / 125000
  | 4 => 7537 / 200000
  | 5 => 22231 / 1000000
  | 6 => 3611 / 250000
  | 7 => 627 / 62500
  | 8 => 1829 / 250000
  | 9 => 5537 / 1000000
  | 10 => 1079 / 250000
  | 11 => 689 / 200000
  | 12 => 701 / 250000
  | 13 => 2321 / 1000000
  | 14 => 487 / 250000
  | 15 => 331 / 200000
  | 16 => 71 / 50000
  | _ => 0

theorem backlund_right_cell23_scalar :
    Real.log (backlundDirichletEnvelope 16 (473 / 200 : ℝ)) ≤ 421 / 1250 := by
  have h := backlund_right_cell_log_certificate
    (a := 473 / 200) (l := 421 / 1250) (v := 1400343 / 1000000)
    (qt := 7569 / 2000) (ut := 3329 / 200000) rightCell23Q rightCell23U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell23Q, rightCell23U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell23U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell23 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 23 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      421 / 1250 := by
  have ha := backlund_right_cell_sigma (j := 23) (a := 473 / 200) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (473 / 200 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell23_scalar

#print axioms backlund_right_cell23_scalar
#print axioms backlund_right_cell23

end LiuWang.Proof.Campaign20260915.RosserCount
