import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell02Q : ℕ → ℚ
  | 2 => 17801 / 10000
  | 3 => 14107 / 5000
  | 4 => 17801 / 5000
  | 5 => 41333 / 10000
  | 6 => 9203 / 2000
  | 7 => 24987 / 5000
  | 8 => 13351 / 2500
  | 9 => 56429 / 10000
  | 10 => 29567 / 5000
  | 11 => 30791 / 5000
  | 12 => 63817 / 10000
  | 13 => 65873 / 10000
  | 14 => 4236 / 625
  | 15 => 17387 / 2500
  | 16 => 14241 / 2000
  | _ => 0

private def rightCell02U : ℕ → ℚ
  | 1 => 1
  | 2 => 84311 / 500000
  | 3 => 59523 / 1000000
  | 4 => 14217 / 500000
  | 5 => 1603 / 100000
  | 6 => 10037 / 1000000
  | 7 => 1689 / 250000
  | 8 => 2397 / 500000
  | 9 => 3543 / 1000000
  | 10 => 2703 / 1000000
  | 11 => 2117 / 1000000
  | 12 => 1693 / 1000000
  | 13 => 689 / 500000
  | 14 => 57 / 50000
  | 15 => 191 / 200000
  | 16 => 809 / 1000000
  | _ => 0

theorem backlund_right_cell02_scalar :
    Real.log (backlundDirichletEnvelope 16 (12841 / 5000 : ℝ)) ≤ 172 / 625 := by
  have h := backlund_right_cell_log_certificate
    (a := 12841 / 5000) (l := 172 / 625) (v := 658391 / 500000)
    (qt := 43479 / 10000) (ut := 1031 / 125000) rightCell02Q rightCell02U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell02Q, rightCell02U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell02U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell02 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 2 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      172 / 625 := by
  have ha := backlund_right_cell_sigma (j := 2) (a := 12841 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (12841 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell02_scalar

#print axioms backlund_right_cell02_scalar
#print axioms backlund_right_cell02

end LiuWang.Proof.Campaign20260915.RosserCount
