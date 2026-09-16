import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell32Q : ℕ → ℚ
  | 2 => 3783 / 2500
  | 3 => 1499 / 625
  | 4 => 6053 / 2000
  | 5 => 35137 / 10000
  | 6 => 39117 / 10000
  | 7 => 42483 / 10000
  | 8 => 22699 / 5000
  | 9 => 47969 / 10000
  | 10 => 5027 / 1000
  | 11 => 1047 / 200
  | 12 => 217 / 40
  | 13 => 55997 / 10000
  | 14 => 11523 / 2000
  | 15 => 29561 / 5000
  | 16 => 60531 / 10000
  | _ => 0

private def rightCell32U : ℕ → ℚ
  | 1 => 1
  | 2 => 44041 / 200000
  | 3 => 5679 / 62500
  | 4 => 24243 / 500000
  | 5 => 29787 / 1000000
  | 6 => 20007 / 1000000
  | 7 => 14289 / 1000000
  | 8 => 2669 / 250000
  | 9 => 129 / 15625
  | 10 => 6559 / 1000000
  | 11 => 5327 / 1000000
  | 12 => 2203 / 500000
  | 13 => 3699 / 1000000
  | 14 => 3147 / 1000000
  | 15 => 2707 / 1000000
  | 16 => 2351 / 1000000
  | _ => 0

theorem backlund_right_cell32_scalar :
    Real.log (backlundDirichletEnvelope 16 (2729 / 1250 : ℝ)) ≤ 509 / 1250 := by
  have h := backlund_right_cell_log_certificate
    (a := 2729 / 1250) (l := 509 / 1250) (v := 1502553 / 1000000)
    (qt := 6561 / 2000) (ut := 31787 / 1000000) rightCell32Q rightCell32U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell32Q, rightCell32U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell32U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell32 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 32 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      509 / 1250 := by
  have ha := backlund_right_cell_sigma (j := 32) (a := 2729 / 1250) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2729 / 1250 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell32_scalar

#print axioms backlund_right_cell32_scalar
#print axioms backlund_right_cell32

end LiuWang.Proof.Campaign20260915.RosserCount
