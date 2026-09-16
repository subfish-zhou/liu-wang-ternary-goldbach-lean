import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell22Q : ℕ → ℚ
  | 2 => 1651 / 1000
  | 3 => 3271 / 1250
  | 4 => 33021 / 10000
  | 5 => 2396 / 625
  | 6 => 42679 / 10000
  | 7 => 46351 / 10000
  | 8 => 12383 / 2500
  | 9 => 52337 / 10000
  | 10 => 54847 / 10000
  | 11 => 57117 / 10000
  | 12 => 5919 / 1000
  | 13 => 61097 / 10000
  | 14 => 31431 / 5000
  | 15 => 12901 / 2000
  | 16 => 66043 / 10000
  | _ => 0

private def rightCell22U : ℕ → ℚ
  | 1 => 1
  | 2 => 95929 / 500000
  | 3 => 73037 / 1000000
  | 4 => 18403 / 500000
  | 5 => 338 / 15625
  | 6 => 3503 / 250000
  | 7 => 4853 / 500000
  | 8 => 7061 / 1000000
  | 9 => 2667 / 500000
  | 10 => 83 / 20000
  | 11 => 827 / 250000
  | 12 => 42 / 15625
  | 13 => 1111 / 500000
  | 14 => 931 / 500000
  | 15 => 79 / 50000
  | 16 => 271 / 200000
  | _ => 0

theorem backlund_right_cell22_scalar :
    Real.log (backlundDirichletEnvelope 16 (1191 / 500 : ℝ)) ≤ 331 / 1000 := by
  have h := backlund_right_cell_log_certificate
    (a := 1191 / 500) (l := 331 / 1000) (v := 696147 / 500000)
    (qt := 38317 / 10000) (ut := 15683 / 1000000) rightCell22Q rightCell22U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell22Q, rightCell22U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell22U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell22 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 22 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      331 / 1000 := by
  have ha := backlund_right_cell_sigma (j := 22) (a := 1191 / 500) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (1191 / 500 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell22_scalar

#print axioms backlund_right_cell22_scalar
#print axioms backlund_right_cell22

end LiuWang.Proof.Campaign20260915.RosserCount
