import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell34Q : ℕ → ℚ
  | 2 => 14807 / 10000
  | 3 => 23469 / 10000
  | 4 => 5923 / 2000
  | 5 => 17191 / 5000
  | 6 => 38277 / 10000
  | 7 => 4157 / 1000
  | 8 => 44423 / 10000
  | 9 => 46939 / 10000
  | 10 => 4919 / 1000
  | 11 => 25613 / 5000
  | 12 => 10617 / 2000
  | 13 => 27397 / 5000
  | 14 => 28189 / 5000
  | 15 => 14463 / 2500
  | 16 => 5923 / 1000
  | _ => 0

private def rightCell34U : ℕ → ℚ
  | 1 => 1
  | 2 => 227479 / 1000000
  | 3 => 47833 / 500000
  | 4 => 25871 / 500000
  | 5 => 32123 / 1000000
  | 6 => 68 / 3125
  | 7 => 3131 / 200000
  | 8 => 11769 / 1000000
  | 9 => 9151 / 1000000
  | 10 => 7307 / 1000000
  | 11 => 5961 / 1000000
  | 12 => 99 / 20000
  | 13 => 1043 / 250000
  | 14 => 3561 / 1000000
  | 15 => 3073 / 1000000
  | 16 => 1339 / 500000
  | _ => 0

theorem backlund_right_cell34_scalar :
    Real.log (backlundDirichletEnvelope 16 (21363 / 10000 : ℝ)) ≤ 1071 / 2500 := by
  have h := backlund_right_cell_log_certificate
    (a := 21363 / 10000) (l := 1071 / 2500) (v := 191843 / 125000)
    (qt := 1969 / 625) (ut := 37697 / 1000000) rightCell34Q rightCell34U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell34Q, rightCell34U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell34U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell34 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 34 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      1071 / 2500 := by
  have ha := backlund_right_cell_sigma (j := 34) (a := 21363 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (21363 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell34_scalar

#print axioms backlund_right_cell34_scalar
#print axioms backlund_right_cell34

end LiuWang.Proof.Campaign20260915.RosserCount
