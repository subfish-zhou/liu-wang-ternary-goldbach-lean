import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell56Q : ℕ → ℚ
  | 2 => 653 / 625
  | 3 => 207 / 125
  | 4 => 1306 / 625
  | 5 => 1213 / 500
  | 6 => 1688 / 625
  | 7 => 7333 / 2500
  | 8 => 6269 / 2000
  | 9 => 414 / 125
  | 10 => 34709 / 10000
  | 11 => 7229 / 2000
  | 12 => 37457 / 10000
  | 13 => 4833 / 1250
  | 14 => 39781 / 10000
  | 15 => 40821 / 10000
  | 16 => 41793 / 10000
  | _ => 0

private def rightCell56U : ℕ → ℚ
  | 1 => 1
  | 2 => 351763 / 1000000
  | 3 => 95451 / 500000
  | 4 => 123737 / 1000000
  | 5 => 8839 / 100000
  | 6 => 4197 / 62500
  | 7 => 53227 / 1000000
  | 8 => 21761 / 500000
  | 9 => 9111 / 250000
  | 10 => 3109 / 100000
  | 11 => 26931 / 1000000
  | 12 => 1181 / 50000
  | 13 => 10467 / 500000
  | 14 => 9361 / 500000
  | 15 => 2109 / 125000
  | 16 => 1531 / 100000
  | _ => 0

theorem backlund_right_cell56_scalar :
    Real.log (backlundDirichletEnvelope 16 (7537 / 5000 : ℝ)) ≤ 4761 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 7537 / 5000) (l := 4761 / 5000) (v := 647831 / 250000)
    (qt := 3517 / 2500) (ut := 120677 / 250000) rightCell56Q rightCell56U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell56Q, rightCell56U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell56U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell56 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 56 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      4761 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 56) (a := 7537 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (7537 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell56_scalar

#print axioms backlund_right_cell56_scalar
#print axioms backlund_right_cell56

end LiuWang.Proof.Campaign20260915.RosserCount
