import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell51Q : ℕ → ℚ
  | 2 => 11533 / 10000
  | 3 => 18279 / 10000
  | 4 => 11533 / 5000
  | 5 => 26779 / 10000
  | 6 => 29813 / 10000
  | 7 => 32377 / 10000
  | 8 => 34599 / 10000
  | 9 => 36559 / 10000
  | 10 => 4789 / 1250
  | 11 => 19949 / 5000
  | 12 => 20673 / 5000
  | 13 => 21339 / 5000
  | 14 => 43911 / 10000
  | 15 => 45059 / 10000
  | 16 => 46133 / 10000
  | _ => 0

private def rightCell51U : ℕ → ℚ
  | 1 => 1
  | 2 => 157797 / 500000
  | 3 => 160751 / 1000000
  | 4 => 249 / 2500
  | 5 => 17177 / 250000
  | 6 => 50727 / 1000000
  | 7 => 7851 / 200000
  | 8 => 31433 / 1000000
  | 9 => 25839 / 1000000
  | 10 => 5421 / 250000
  | 11 => 2313 / 125000
  | 12 => 1601 / 100000
  | 13 => 14013 / 1000000
  | 14 => 3097 / 250000
  | 15 => 2761 / 250000
  | 16 => 31 / 3125
  | _ => 0

theorem backlund_right_cell51_scalar :
    Real.log (backlundDirichletEnvelope 16 (16639 / 10000 : ℝ)) ≤ 7583 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 16639 / 10000) (l := 7583 / 10000) (v := 1067261 / 500000)
    (qt := 18407 / 10000) (ut := 59763 / 250000) rightCell51Q rightCell51U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell51Q, rightCell51U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell51U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell51 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 51 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      7583 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 51) (a := 16639 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (16639 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell51_scalar

#print axioms backlund_right_cell51_scalar
#print axioms backlund_right_cell51

end LiuWang.Proof.Campaign20260915.RosserCount
