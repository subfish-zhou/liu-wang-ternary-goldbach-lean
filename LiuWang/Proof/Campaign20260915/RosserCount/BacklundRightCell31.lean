import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell31Q : ℕ → ℚ
  | 2 => 15289 / 10000
  | 3 => 24233 / 10000
  | 4 => 15289 / 5000
  | 5 => 71 / 20
  | 6 => 19761 / 5000
  | 7 => 21461 / 5000
  | 8 => 11467 / 2500
  | 9 => 24233 / 5000
  | 10 => 5079 / 1000
  | 11 => 13223 / 2500
  | 12 => 13703 / 2500
  | 13 => 56577 / 10000
  | 14 => 14553 / 2500
  | 15 => 29867 / 5000
  | 16 => 61157 / 10000
  | _ => 0

private def rightCell31U : ℕ → ℚ
  | 1 => 1
  | 2 => 108387 / 500000
  | 3 => 88629 / 1000000
  | 4 => 46991 / 1000000
  | 5 => 1149 / 40000
  | 6 => 19213 / 1000000
  | 7 => 547 / 40000
  | 8 => 5093 / 500000
  | 9 => 491 / 62500
  | 10 => 6227 / 1000000
  | 11 => 2523 / 500000
  | 12 => 833 / 200000
  | 13 => 3491 / 1000000
  | 14 => 593 / 200000
  | 15 => 1273 / 500000
  | 16 => 69 / 31250
  | _ => 0

theorem backlund_right_cell31_scalar :
    Real.log (backlundDirichletEnvelope 16 (11029 / 5000 : ℝ)) ≤ 159 / 400 := by
  have h := backlund_right_cell_log_certificate
    (a := 11029 / 5000) (l := 159 / 400) (v := 297599 / 200000)
    (qt := 33431 / 10000) (ut := 14649 / 500000) rightCell31Q rightCell31U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell31Q, rightCell31U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell31U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell31 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 31 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      159 / 400 := by
  have ha := backlund_right_cell_sigma (j := 31) (a := 11029 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (11029 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell31_scalar

#print axioms backlund_right_cell31_scalar
#print axioms backlund_right_cell31

end LiuWang.Proof.Campaign20260915.RosserCount
