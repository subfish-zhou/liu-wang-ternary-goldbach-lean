import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell24Q : ℕ → ℚ
  | 2 => 1627 / 1000
  | 3 => 6447 / 2500
  | 4 => 32541 / 10000
  | 5 => 37779 / 10000
  | 6 => 42059 / 10000
  | 7 => 22839 / 5000
  | 8 => 12203 / 2500
  | 9 => 51577 / 10000
  | 10 => 1081 / 200
  | 11 => 3518 / 625
  | 12 => 5833 / 1000
  | 13 => 60209 / 10000
  | 14 => 61949 / 10000
  | 15 => 3973 / 625
  | 16 => 65083 / 10000
  | _ => 0

private def rightCell24U : ℕ → ℚ
  | 1 => 1
  | 2 => 196519 / 1000000
  | 3 => 15173 / 200000
  | 4 => 4827 / 125000
  | 5 => 22871 / 1000000
  | 6 => 3727 / 250000
  | 7 => 10381 / 1000000
  | 8 => 1897 / 250000
  | 9 => 1151 / 200000
  | 10 => 899 / 200000
  | 11 => 3593 / 1000000
  | 12 => 293 / 100000
  | 13 => 607 / 250000
  | 14 => 51 / 25000
  | 15 => 347 / 200000
  | 16 => 373 / 250000
  | _ => 0

theorem backlund_right_cell24_scalar :
    Real.log (backlundDirichletEnvelope 16 (11737 / 5000 : ℝ)) ≤ 3429 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 11737 / 5000) (l := 3429 / 10000) (v := 704461 / 500000)
    (qt := 37357 / 10000) (ut := 8853 / 500000) rightCell24Q rightCell24U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell24Q, rightCell24U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell24U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell24 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 24 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3429 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 24) (a := 11737 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (11737 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell24_scalar

#print axioms backlund_right_cell24_scalar
#print axioms backlund_right_cell24

end LiuWang.Proof.Campaign20260915.RosserCount
