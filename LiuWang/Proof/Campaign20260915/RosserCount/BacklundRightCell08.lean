import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell08Q : ℕ → ℚ
  | 2 => 17637 / 10000
  | 3 => 13977 / 5000
  | 4 => 17637 / 5000
  | 5 => 5119 / 1250
  | 6 => 45591 / 10000
  | 7 => 49513 / 10000
  | 8 => 52911 / 10000
  | 9 => 13977 / 2500
  | 10 => 58589 / 10000
  | 11 => 30507 / 5000
  | 12 => 15807 / 2500
  | 13 => 13053 / 2000
  | 14 => 1343 / 200
  | 15 => 34453 / 5000
  | 16 => 17637 / 2500
  | _ => 0

private def rightCell08U : ℕ → ℚ
  | 1 => 1
  | 2 => 17141 / 100000
  | 3 => 61091 / 1000000
  | 4 => 14691 / 500000
  | 5 => 16653 / 1000000
  | 6 => 1309 / 125000
  | 7 => 283 / 40000
  | 8 => 5037 / 1000000
  | 9 => 3733 / 1000000
  | 10 => 571 / 200000
  | 11 => 7 / 3125
  | 12 => 359 / 200000
  | 13 => 293 / 200000
  | 14 => 1213 / 1000000
  | 15 => 509 / 500000
  | 16 => 27 / 31250
  | _ => 0

theorem backlund_right_cell08_scalar :
    Real.log (backlundDirichletEnvelope 16 (5089 / 2000 : ℝ)) ≤ 176 / 625 := by
  have h := backlund_right_cell_log_certificate
    (a := 5089 / 2000) (l := 176 / 625) (v := 662623 / 500000)
    (qt := 21411 / 5000) (ut := 8943 / 1000000) rightCell08Q rightCell08U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell08Q, rightCell08U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell08U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell08 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 8 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      176 / 625 := by
  have ha := backlund_right_cell_sigma (j := 8) (a := 5089 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (5089 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell08_scalar

#print axioms backlund_right_cell08_scalar
#print axioms backlund_right_cell08

end LiuWang.Proof.Campaign20260915.RosserCount
