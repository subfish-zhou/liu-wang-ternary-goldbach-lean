import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell36Q : ℕ → ℚ
  | 2 => 14467 / 10000
  | 3 => 2293 / 1000
  | 4 => 14467 / 5000
  | 5 => 4199 / 1250
  | 6 => 37397 / 10000
  | 7 => 8123 / 2000
  | 8 => 21701 / 5000
  | 9 => 2293 / 500
  | 10 => 48059 / 10000
  | 11 => 3128 / 625
  | 12 => 6483 / 1250
  | 13 => 10707 / 2000
  | 14 => 27541 / 5000
  | 15 => 28261 / 5000
  | 16 => 57869 / 10000
  | _ => 0

private def rightCell36U : ℕ → ℚ
  | 1 => 1
  | 2 => 117673 / 500000
  | 3 => 25241 / 250000
  | 4 => 13847 / 250000
  | 5 => 8691 / 250000
  | 6 => 11881 / 500000
  | 7 => 2153 / 125000
  | 8 => 6517 / 500000
  | 9 => 5097 / 500000
  | 10 => 4091 / 500000
  | 11 => 3353 / 500000
  | 12 => 5593 / 1000000
  | 13 => 1183 / 250000
  | 14 => 2027 / 500000
  | 15 => 351 / 100000
  | 16 => 767 / 250000
  | _ => 0

theorem backlund_right_cell36_scalar :
    Real.log (backlundDirichletEnvelope 16 (2609 / 1250 : ℝ)) ≤ 2261 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 2609 / 1250) (l := 2261 / 5000) (v := 314333 / 200000)
    (qt := 30143 / 10000) (ut := 5643 / 125000) rightCell36Q rightCell36U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell36Q, rightCell36U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell36U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell36 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 36 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2261 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 36) (a := 2609 / 1250) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2609 / 1250 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell36_scalar

#print axioms backlund_right_cell36_scalar
#print axioms backlund_right_cell36

end LiuWang.Proof.Campaign20260915.RosserCount
