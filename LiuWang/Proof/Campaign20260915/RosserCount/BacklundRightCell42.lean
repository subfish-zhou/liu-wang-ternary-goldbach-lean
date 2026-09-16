import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell42Q : ℕ → ℚ
  | 2 => 13367 / 10000
  | 3 => 10593 / 5000
  | 4 => 13367 / 5000
  | 5 => 31037 / 10000
  | 6 => 17277 / 5000
  | 7 => 18763 / 5000
  | 8 => 20051 / 5000
  | 9 => 42373 / 10000
  | 10 => 8881 / 2000
  | 11 => 46243 / 10000
  | 12 => 47921 / 10000
  | 13 => 9893 / 2000
  | 14 => 25447 / 5000
  | 15 => 3264 / 625
  | 16 => 53469 / 10000
  | _ => 0

private def rightCell42U : ℕ → ℚ
  | 1 => 1
  | 2 => 32839 / 125000
  | 3 => 601 / 5000
  | 4 => 34509 / 500000
  | 5 => 44883 / 1000000
  | 6 => 1263 / 40000
  | 7 => 23457 / 1000000
  | 8 => 1813 / 100000
  | 9 => 14447 / 1000000
  | 10 => 11791 / 1000000
  | 11 => 9811 / 1000000
  | 12 => 1037 / 125000
  | 13 => 7109 / 1000000
  | 14 => 3081 / 500000
  | 15 => 1079 / 200000
  | 16 => 4763 / 1000000
  | _ => 0

theorem backlund_right_cell42_scalar :
    Real.log (backlundDirichletEnvelope 16 (3857 / 2000 : ℝ)) ≤ 5423 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 3857 / 2000) (l := 5423 / 10000) (v := 68793 / 40000)
    (qt := 25743 / 10000) (ut := 20519 / 250000) rightCell42Q rightCell42U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell42Q, rightCell42U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell42U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell42 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 42 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      5423 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 42) (a := 3857 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (3857 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell42_scalar

#print axioms backlund_right_cell42_scalar
#print axioms backlund_right_cell42

end LiuWang.Proof.Campaign20260915.RosserCount
