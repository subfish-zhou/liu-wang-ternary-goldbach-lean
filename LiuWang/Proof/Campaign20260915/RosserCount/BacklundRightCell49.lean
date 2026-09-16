import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell49Q : ℕ → ℚ
  | 2 => 2989 / 2500
  | 3 => 18949 / 10000
  | 4 => 2989 / 1250
  | 5 => 27761 / 10000
  | 6 => 15453 / 5000
  | 7 => 8391 / 2500
  | 8 => 8967 / 2500
  | 9 => 37899 / 10000
  | 10 => 39717 / 10000
  | 11 => 41361 / 10000
  | 12 => 21431 / 5000
  | 13 => 22121 / 5000
  | 14 => 45521 / 10000
  | 15 => 46711 / 10000
  | 16 => 2989 / 625
  | _ => 0

private def rightCell49U : ℕ → ℚ
  | 1 => 1
  | 2 => 302523 / 1000000
  | 3 => 75167 / 500000
  | 4 => 286 / 3125
  | 5 => 62281 / 1000000
  | 6 => 1819 / 40000
  | 7 => 34861 / 1000000
  | 8 => 27687 / 1000000
  | 9 => 11299 / 500000
  | 10 => 9421 / 500000
  | 11 => 7993 / 500000
  | 12 => 6879 / 500000
  | 13 => 749 / 62500
  | 14 => 5273 / 500000
  | 15 => 4681 / 500000
  | 16 => 1047 / 125000
  | _ => 0

theorem backlund_right_cell49_scalar :
    Real.log (backlundDirichletEnvelope 16 (17249 / 10000 : ℝ)) ≤ 6987 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 17249 / 10000) (l := 6987 / 10000) (v := 31422 / 15625)
    (qt := 10049 / 5000) (ut := 1479 / 8000) rightCell49Q rightCell49U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell49Q, rightCell49U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell49U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell49 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 49 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      6987 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 49) (a := 17249 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (17249 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell49_scalar

#print axioms backlund_right_cell49_scalar
#print axioms backlund_right_cell49

end LiuWang.Proof.Campaign20260915.RosserCount
