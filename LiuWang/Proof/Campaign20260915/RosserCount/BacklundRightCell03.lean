import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell03Q : ℕ → ℚ
  | 2 => 4447 / 2500
  | 3 => 28193 / 10000
  | 4 => 4447 / 1250
  | 5 => 20651 / 5000
  | 6 => 45981 / 10000
  | 7 => 49937 / 10000
  | 8 => 13341 / 2500
  | 9 => 56387 / 10000
  | 10 => 59091 / 10000
  | 11 => 61537 / 10000
  | 12 => 6377 / 1000
  | 13 => 4114 / 625
  | 14 => 33863 / 5000
  | 15 => 8687 / 1250
  | 16 => 4447 / 625
  | _ => 0

private def rightCell03U : ℕ → ℚ
  | 1 => 1
  | 2 => 168841 / 1000000
  | 3 => 932 / 15625
  | 4 => 7127 / 250000
  | 5 => 201 / 12500
  | 6 => 10071 / 1000000
  | 7 => 6781 / 1000000
  | 8 => 2407 / 500000
  | 9 => 1779 / 500000
  | 10 => 543 / 200000
  | 11 => 1063 / 500000
  | 12 => 1701 / 1000000
  | 13 => 277 / 200000
  | 14 => 229 / 200000
  | 15 => 3 / 3125
  | 16 => 813 / 1000000
  | _ => 0

theorem backlund_right_cell03_scalar :
    Real.log (backlundDirichletEnvelope 16 (25663 / 10000 : ℝ)) ≤ 2757 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 25663 / 10000) (l := 2757 / 10000) (v := 1317447 / 1000000)
    (qt := 43427 / 10000) (ut := 8301 / 1000000) rightCell03Q rightCell03U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell03Q, rightCell03U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell03U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell03 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 3 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2757 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 3) (a := 25663 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (25663 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell03_scalar

#print axioms backlund_right_cell03_scalar
#print axioms backlund_right_cell03

end LiuWang.Proof.Campaign20260915.RosserCount
