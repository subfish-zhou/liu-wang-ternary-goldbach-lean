import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell16Q : ℕ → ℚ
  | 2 => 4279 / 2500
  | 3 => 27129 / 10000
  | 4 => 34233 / 10000
  | 5 => 39743 / 10000
  | 6 => 8849 / 2000
  | 7 => 12013 / 2500
  | 8 => 51349 / 10000
  | 9 => 27129 / 5000
  | 10 => 2843 / 500
  | 11 => 59213 / 10000
  | 12 => 30681 / 5000
  | 13 => 31669 / 5000
  | 14 => 4073 / 625
  | 15 => 8359 / 1250
  | 16 => 34233 / 5000
  | _ => 0

private def rightCell16U : ℕ → ℚ
  | 1 => 1
  | 2 => 180577 / 1000000
  | 3 => 13269 / 200000
  | 4 => 6521 / 200000
  | 5 => 18793 / 1000000
  | 6 => 11981 / 1000000
  | 7 => 2047 / 250000
  | 8 => 92 / 15625
  | 9 => 2201 / 500000
  | 10 => 1697 / 500000
  | 11 => 1341 / 500000
  | 12 => 541 / 250000
  | 13 => 111 / 62500
  | 14 => 1479 / 1000000
  | 15 => 1247 / 1000000
  | 16 => 133 / 125000
  | _ => 0

theorem backlund_right_cell16_scalar :
    Real.log (backlundDirichletEnvelope 16 (12347 / 5000 : ℝ)) ≤ 379 / 1250 := by
  have h := backlund_right_cell_log_certificate
    (a := 12347 / 5000) (l := 379 / 1250) (v := 1354161 / 1000000)
    (qt := 2037 / 500) (ut := 1447 / 125000) rightCell16Q rightCell16U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell16Q, rightCell16U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell16U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell16 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 16 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      379 / 1250 := by
  have ha := backlund_right_cell_sigma (j := 16) (a := 12347 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (12347 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell16_scalar

#print axioms backlund_right_cell16_scalar
#print axioms backlund_right_cell16

end LiuWang.Proof.Campaign20260915.RosserCount
