import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell10Q : ℕ → ℚ
  | 2 => 8769 / 5000
  | 3 => 13899 / 5000
  | 4 => 35077 / 10000
  | 5 => 40723 / 10000
  | 6 => 5667 / 1250
  | 7 => 49237 / 10000
  | 8 => 6577 / 1250
  | 9 => 13899 / 2500
  | 10 => 29131 / 5000
  | 11 => 60673 / 10000
  | 12 => 503 / 80
  | 13 => 649 / 100
  | 14 => 8347 / 1250
  | 15 => 68521 / 10000
  | 16 => 35077 / 5000
  | _ => 0

private def rightCell10U : ℕ → ℚ
  | 1 => 1
  | 2 => 34623 / 200000
  | 3 => 62051 / 1000000
  | 4 => 14983 / 500000
  | 5 => 17039 / 1000000
  | 6 => 5371 / 500000
  | 7 => 7273 / 1000000
  | 8 => 5187 / 1000000
  | 9 => 3851 / 1000000
  | 10 => 59 / 20000
  | 11 => 1159 / 500000
  | 12 => 93 / 50000
  | 13 => 1519 / 1000000
  | 14 => 1259 / 1000000
  | 15 => 529 / 500000
  | 16 => 449 / 500000
  | _ => 0

theorem backlund_right_cell10_scalar :
    Real.log (backlundDirichletEnvelope 16 (25303 / 10000 : ℝ)) ≤ 357 / 1250 := by
  have h := backlund_right_cell_log_certificate
    (a := 25303 / 10000) (l := 357 / 1250) (v := 53219 / 40000)
    (qt := 10607 / 2500) (ut := 9389 / 1000000) rightCell10Q rightCell10U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell10Q, rightCell10U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell10U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell10 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 10 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      357 / 1250 := by
  have ha := backlund_right_cell_sigma (j := 10) (a := 25303 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (25303 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell10_scalar

#print axioms backlund_right_cell10_scalar
#print axioms backlund_right_cell10

end LiuWang.Proof.Campaign20260915.RosserCount
