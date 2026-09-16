import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell48Q : ℕ → ℚ
  | 2 => 3041 / 2500
  | 3 => 241 / 125
  | 4 => 24329 / 10000
  | 5 => 5649 / 2000
  | 6 => 6289 / 2000
  | 7 => 683 / 200
  | 8 => 18247 / 5000
  | 9 => 38561 / 10000
  | 10 => 4041 / 1000
  | 11 => 42083 / 10000
  | 12 => 4361 / 1000
  | 13 => 22507 / 5000
  | 14 => 9263 / 2000
  | 15 => 23763 / 5000
  | 16 => 24329 / 5000
  | _ => 0

private def rightCell48U : ℕ → ℚ
  | 1 => 1
  | 2 => 59259 / 200000
  | 3 => 145439 / 1000000
  | 4 => 43891 / 500000
  | 5 => 59339 / 1000000
  | 6 => 43089 / 1000000
  | 7 => 32877 / 1000000
  | 8 => 26007 / 1000000
  | 9 => 21151 / 1000000
  | 10 => 879 / 50000
  | 11 => 1859 / 125000
  | 12 => 6383 / 500000
  | 13 => 5547 / 500000
  | 14 => 9741 / 1000000
  | 15 => 863 / 100000
  | 16 => 3853 / 500000
  | _ => 0

theorem backlund_right_cell48_scalar :
    Real.log (backlundDirichletEnvelope 16 (351 / 200 : ℝ)) ≤ 3359 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 351 / 200) (l := 3359 / 5000) (v := 1957653 / 1000000)
    (qt := 20933 / 10000) (ut := 32657 / 200000) rightCell48Q rightCell48U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell48Q, rightCell48U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell48U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell48 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 48 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3359 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 48) (a := 351 / 200) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (351 / 200 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell48_scalar

#print axioms backlund_right_cell48_scalar
#print axioms backlund_right_cell48

end LiuWang.Proof.Campaign20260915.RosserCount
