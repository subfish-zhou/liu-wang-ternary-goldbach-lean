import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell58Q : ℕ → ℚ
  | 2 => 2001 / 2000
  | 3 => 7929 / 5000
  | 4 => 20011 / 10000
  | 5 => 1452 / 625
  | 6 => 3233 / 1250
  | 7 => 28089 / 10000
  | 8 => 1876 / 625
  | 9 => 7929 / 2500
  | 10 => 33237 / 10000
  | 11 => 34613 / 10000
  | 12 => 35869 / 10000
  | 13 => 1481 / 400
  | 14 => 19047 / 5000
  | 15 => 3909 / 1000
  | 16 => 20011 / 5000
  | _ => 0

private def rightCell58U : ℕ → ℚ
  | 1 => 1
  | 2 => 22981 / 62500
  | 3 => 12799 / 62500
  | 4 => 135187 / 1000000
  | 5 => 2449 / 25000
  | 6 => 75291 / 1000000
  | 7 => 3767 / 62500
  | 8 => 12427 / 250000
  | 9 => 41937 / 1000000
  | 10 => 1801 / 50000
  | 11 => 31389 / 1000000
  | 12 => 5537 / 200000
  | 13 => 12331 / 500000
  | 14 => 11081 / 500000
  | 15 => 20061 / 1000000
  | 16 => 4569 / 250000
  | _ => 0

theorem backlund_right_cell58_scalar :
    Real.log (backlundDirichletEnvelope 16 (2887 / 2000 : ℝ)) ≤ 1319 / 1250 := by
  have h := backlund_right_cell_log_certificate
    (a := 2887 / 2000) (l := 1319 / 1250) (v := 2872413 / 1000000)
    (qt := 1537 / 1250) (ut := 659323 / 1000000) rightCell58Q rightCell58U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell58Q, rightCell58U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell58U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell58 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 58 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      1319 / 1250 := by
  have ha := backlund_right_cell_sigma (j := 58) (a := 2887 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2887 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell58_scalar

#print axioms backlund_right_cell58_scalar
#print axioms backlund_right_cell58

end LiuWang.Proof.Campaign20260915.RosserCount
