import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell19Q : ℕ → ℚ
  | 2 => 3367 / 2000
  | 3 => 6671 / 2500
  | 4 => 33671 / 10000
  | 5 => 39091 / 10000
  | 6 => 544 / 125
  | 7 => 2954 / 625
  | 8 => 50507 / 10000
  | 9 => 6671 / 1250
  | 10 => 55927 / 10000
  | 11 => 29121 / 5000
  | 12 => 12071 / 2000
  | 13 => 623 / 100
  | 14 => 641 / 100
  | 15 => 2631 / 400
  | 16 => 67343 / 10000
  | _ => 0

private def rightCell19U : ℕ → ℚ
  | 1 => 1
  | 2 => 185723 / 1000000
  | 3 => 17341 / 250000
  | 4 => 3449 / 100000
  | 5 => 20059 / 1000000
  | 6 => 6441 / 500000
  | 7 => 8859 / 1000000
  | 8 => 1281 / 200000
  | 9 => 1203 / 250000
  | 10 => 149 / 40000
  | 11 => 739 / 250000
  | 12 => 2393 / 1000000
  | 13 => 197 / 100000
  | 14 => 823 / 500000
  | 15 => 87 / 62500
  | 16 => 119 / 100000
  | _ => 0

theorem backlund_right_cell19_scalar :
    Real.log (backlundDirichletEnvelope 16 (24289 / 10000 : ℝ)) ≤ 3157 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 24289 / 10000) (l := 3157 / 10000) (v := 274237 / 200000)
    (qt := 39617 / 10000) (ut := 13319 / 1000000) rightCell19Q rightCell19U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell19Q, rightCell19U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell19U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell19 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 19 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3157 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 19) (a := 24289 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (24289 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell19_scalar

#print axioms backlund_right_cell19_scalar
#print axioms backlund_right_cell19

end LiuWang.Proof.Campaign20260915.RosserCount
