import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell04Q : ℕ → ℚ
  | 2 => 2221 / 1250
  | 3 => 14081 / 5000
  | 4 => 35537 / 10000
  | 5 => 41257 / 10000
  | 6 => 45931 / 10000
  | 7 => 49883 / 10000
  | 8 => 26653 / 5000
  | 9 => 2253 / 400
  | 10 => 29513 / 5000
  | 11 => 6147 / 1000
  | 12 => 637 / 100
  | 13 => 8219 / 1250
  | 14 => 16913 / 2500
  | 15 => 3471 / 500
  | 16 => 2843 / 400
  | _ => 0

private def rightCell04U : ℕ → ℚ
  | 1 => 1
  | 2 => 169179 / 1000000
  | 3 => 59833 / 1000000
  | 4 => 28619 / 1000000
  | 5 => 16153 / 1000000
  | 6 => 5061 / 500000
  | 7 => 3409 / 500000
  | 8 => 2421 / 500000
  | 9 => 179 / 50000
  | 10 => 2733 / 1000000
  | 11 => 107 / 50000
  | 12 => 1713 / 1000000
  | 13 => 279 / 200000
  | 14 => 577 / 500000
  | 15 => 967 / 1000000
  | 16 => 819 / 1000000
  | _ => 0

theorem backlund_right_cell04_scalar :
    Real.log (backlundDirichletEnvelope 16 (5127 / 2000 : ℝ)) ≤ 553 / 2000 := by
  have h := backlund_right_cell_log_certificate
    (a := 5127 / 2000) (l := 553 / 2000) (v := 82403 / 62500)
    (qt := 43349 / 10000) (ut := 8381 / 1000000) rightCell04Q rightCell04U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell04Q, rightCell04U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell04U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell04 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 4 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      553 / 2000 := by
  have ha := backlund_right_cell_sigma (j := 4) (a := 5127 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (5127 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell04_scalar

#print axioms backlund_right_cell04_scalar
#print axioms backlund_right_cell04

end LiuWang.Proof.Campaign20260915.RosserCount
