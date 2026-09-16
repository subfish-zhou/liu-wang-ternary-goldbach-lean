import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell35Q : ℕ → ℚ
  | 2 => 14639 / 10000
  | 3 => 11601 / 5000
  | 4 => 14639 / 5000
  | 5 => 33991 / 10000
  | 6 => 37841 / 10000
  | 7 => 41097 / 10000
  | 8 => 43917 / 10000
  | 9 => 9281 / 2000
  | 10 => 4863 / 1000
  | 11 => 50643 / 10000
  | 12 => 52481 / 10000
  | 13 => 54171 / 10000
  | 14 => 6967 / 1250
  | 15 => 57193 / 10000
  | 16 => 58557 / 10000
  | _ => 0

private def rightCell35U : ℕ → ℚ
  | 1 => 1
  | 2 => 231333 / 1000000
  | 3 => 49127 / 500000
  | 4 => 10703 / 200000
  | 5 => 8351 / 250000
  | 6 => 2273 / 100000
  | 7 => 16413 / 1000000
  | 8 => 619 / 50000
  | 9 => 9653 / 1000000
  | 10 => 483 / 62500
  | 11 => 6319 / 1000000
  | 12 => 2629 / 500000
  | 13 => 4441 / 1000000
  | 14 => 3797 / 1000000
  | 15 => 3283 / 1000000
  | 16 => 179 / 62500
  | _ => 0

theorem backlund_right_cell35_scalar :
    Real.log (backlundDirichletEnvelope 16 (264 / 125 : ℝ)) ≤ 11 / 25 := by
  have h := backlund_right_cell_log_certificate
    (a := 264 / 125) (l := 11 / 25) (v := 62103 / 40000)
    (qt := 30831 / 10000) (ut := 41203 / 1000000) rightCell35Q rightCell35U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell35Q, rightCell35U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell35U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell35 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 35 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      11 / 25 := by
  have ha := backlund_right_cell_sigma (j := 35) (a := 264 / 125) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (264 / 125 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell35_scalar

#print axioms backlund_right_cell35_scalar
#print axioms backlund_right_cell35

end LiuWang.Proof.Campaign20260915.RosserCount
