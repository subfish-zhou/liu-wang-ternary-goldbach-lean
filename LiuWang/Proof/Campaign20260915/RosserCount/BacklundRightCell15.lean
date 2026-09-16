import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell15Q : ℕ → ℚ
  | 2 => 17199 / 10000
  | 3 => 1363 / 500
  | 4 => 34399 / 10000
  | 5 => 2496 / 625
  | 6 => 2223 / 500
  | 7 => 9657 / 2000
  | 8 => 51599 / 10000
  | 9 => 54521 / 10000
  | 10 => 3571 / 625
  | 11 => 59501 / 10000
  | 12 => 3083 / 500
  | 13 => 31823 / 5000
  | 14 => 13097 / 2000
  | 15 => 67197 / 10000
  | 16 => 34399 / 5000
  | _ => 0

private def rightCell15U : ℕ → ℚ
  | 1 => 1
  | 2 => 35817 / 200000
  | 3 => 65481 / 1000000
  | 4 => 8017 / 250000
  | 5 => 9217 / 500000
  | 6 => 5863 / 500000
  | 7 => 7999 / 1000000
  | 8 => 5743 / 1000000
  | 9 => 67 / 15625
  | 10 => 3301 / 1000000
  | 11 => 1303 / 500000
  | 12 => 21 / 10000
  | 13 => 861 / 500000
  | 14 => 1433 / 1000000
  | 15 => 1207 / 1000000
  | 16 => 1029 / 1000000
  | _ => 0

theorem backlund_right_cell15_scalar :
    Real.log (backlundDirichletEnvelope 16 (12407 / 5000 : ℝ)) ≤ 2997 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 12407 / 5000) (l := 2997 / 10000) (v := 84333 / 62500)
    (qt := 41073 / 10000) (ut := 5553 / 500000) rightCell15Q rightCell15U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell15Q, rightCell15U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell15U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell15 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 15 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2997 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 15) (a := 12407 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (12407 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell15_scalar

#print axioms backlund_right_cell15_scalar
#print axioms backlund_right_cell15

end LiuWang.Proof.Campaign20260915.RosserCount
