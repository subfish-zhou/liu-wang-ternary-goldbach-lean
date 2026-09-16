import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell06Q : ℕ → ℚ
  | 2 => 17713 / 10000
  | 3 => 1123 / 400
  | 4 => 17713 / 5000
  | 5 => 41129 / 10000
  | 6 => 11447 / 2500
  | 7 => 49727 / 10000
  | 8 => 2657 / 500
  | 9 => 1123 / 200
  | 10 => 29421 / 5000
  | 11 => 30639 / 5000
  | 12 => 63501 / 10000
  | 13 => 65547 / 10000
  | 14 => 67441 / 10000
  | 15 => 17301 / 2500
  | 16 => 70853 / 10000
  | _ => 0

private def rightCell06U : ℕ → ℚ
  | 1 => 1
  | 2 => 2658 / 15625
  | 3 => 15089 / 250000
  | 4 => 14469 / 500000
  | 5 => 16361 / 1000000
  | 6 => 2567 / 250000
  | 7 => 277 / 40000
  | 8 => 4923 / 1000000
  | 9 => 3643 / 1000000
  | 10 => 87 / 31250
  | 11 => 1091 / 500000
  | 12 => 1747 / 1000000
  | 13 => 89 / 62500
  | 14 => 589 / 500000
  | 15 => 247 / 250000
  | 16 => 419 / 500000
  | _ => 0

theorem backlund_right_cell06_scalar :
    Real.log (backlundDirichletEnvelope 16 (5111 / 2000 : ℝ)) ≤ 2787 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 5111 / 2000) (l := 2787 / 10000) (v := 4129 / 3125)
    (qt := 43127 / 10000) (ut := 8613 / 1000000) rightCell06Q rightCell06U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell06Q, rightCell06U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell06U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell06 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 6 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2787 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 6) (a := 5111 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (5111 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell06_scalar

#print axioms backlund_right_cell06_scalar
#print axioms backlund_right_cell06

end LiuWang.Proof.Campaign20260915.RosserCount
