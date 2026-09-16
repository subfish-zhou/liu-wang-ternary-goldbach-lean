import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell18Q : ℕ → ℚ
  | 2 => 8467 / 5000
  | 3 => 671 / 250
  | 4 => 8467 / 2500
  | 5 => 983 / 250
  | 6 => 21887 / 5000
  | 7 => 2377 / 500
  | 8 => 25401 / 5000
  | 9 => 671 / 125
  | 10 => 28127 / 5000
  | 11 => 29291 / 5000
  | 12 => 15177 / 2500
  | 13 => 7833 / 1250
  | 14 => 32237 / 5000
  | 15 => 827 / 125
  | 16 => 67737 / 10000
  | _ => 0

private def rightCell18U : ℕ → ℚ
  | 1 => 1
  | 2 => 91947 / 500000
  | 3 => 6829 / 100000
  | 4 => 33817 / 1000000
  | 5 => 3921 / 200000
  | 6 => 6279 / 500000
  | 7 => 4309 / 500000
  | 8 => 6219 / 1000000
  | 9 => 583 / 125000
  | 10 => 1803 / 500000
  | 11 => 2857 / 1000000
  | 12 => 231 / 100000
  | 13 => 19 / 10000
  | 14 => 317 / 200000
  | 15 => 1339 / 1000000
  | 16 => 143 / 125000
  | _ => 0

theorem backlund_right_cell18_scalar :
    Real.log (backlundDirichletEnvelope 16 (24431 / 10000 : ℝ)) ≤ 3113 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 24431 / 10000) (l := 3113 / 10000) (v := 341271 / 250000)
    (qt := 40011 / 10000) (ut := 6339 / 500000) rightCell18Q rightCell18U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell18Q, rightCell18U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell18U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell18 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 18 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3113 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 18) (a := 24431 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (24431 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell18_scalar

#print axioms backlund_right_cell18_scalar
#print axioms backlund_right_cell18

end LiuWang.Proof.Campaign20260915.RosserCount
