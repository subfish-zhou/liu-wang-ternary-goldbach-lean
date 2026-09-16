import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell54Q : ℕ → ℚ
  | 2 => 5443 / 5000
  | 3 => 8627 / 5000
  | 4 => 21773 / 10000
  | 5 => 25277 / 10000
  | 6 => 28141 / 10000
  | 7 => 15281 / 5000
  | 8 => 32659 / 10000
  | 9 => 34509 / 10000
  | 10 => 9041 / 2500
  | 11 => 37661 / 10000
  | 12 => 39027 / 10000
  | 13 => 8057 / 2000
  | 14 => 41449 / 10000
  | 15 => 10633 / 2500
  | 16 => 21773 / 5000
  | _ => 0

private def rightCell54U : ℕ → ℚ
  | 1 => 1
  | 2 => 21043 / 62500
  | 3 => 89051 / 500000
  | 4 => 28337 / 250000
  | 5 => 79843 / 1000000
  | 6 => 59959 / 1000000
  | 7 => 47067 / 1000000
  | 8 => 38163 / 1000000
  | 9 => 15859 / 500000
  | 10 => 84 / 3125
  | 11 => 23143 / 1000000
  | 12 => 5047 / 250000
  | 13 => 8901 / 500000
  | 14 => 7923 / 500000
  | 15 => 14219 / 1000000
  | 16 => 803 / 62500
  | _ => 0

theorem backlund_right_cell54_scalar :
    Real.log (backlundDirichletEnvelope 16 (7853 / 5000 : ℝ)) ≤ 1731 / 2000 := by
  have h := backlund_right_cell_log_certificate
    (a := 7853 / 5000) (l := 1731 / 2000) (v := 2376073 / 1000000)
    (qt := 791 / 500) (ut := 360259 / 1000000) rightCell54Q rightCell54U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell54Q, rightCell54U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell54U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell54 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 54 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      1731 / 2000 := by
  have ha := backlund_right_cell_sigma (j := 54) (a := 7853 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (7853 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell54_scalar

#print axioms backlund_right_cell54_scalar
#print axioms backlund_right_cell54

end LiuWang.Proof.Campaign20260915.RosserCount
