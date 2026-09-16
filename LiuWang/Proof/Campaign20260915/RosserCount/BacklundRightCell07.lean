import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell07Q : ℕ → ℚ
  | 2 => 8839 / 5000
  | 3 => 14009 / 5000
  | 4 => 8839 / 2500
  | 5 => 41047 / 10000
  | 6 => 45697 / 10000
  | 7 => 12407 / 2500
  | 8 => 26517 / 5000
  | 9 => 56037 / 10000
  | 10 => 2349 / 400
  | 11 => 12231 / 2000
  | 12 => 507 / 80
  | 13 => 8177 / 1250
  | 14 => 33653 / 5000
  | 15 => 34533 / 5000
  | 16 => 8839 / 1250
  | _ => 0

private def rightCell07U : ℕ → ℚ
  | 1 => 1
  | 2 => 170709 / 1000000
  | 3 => 60701 / 1000000
  | 4 => 14571 / 500000
  | 5 => 3299 / 200000
  | 6 => 5181 / 500000
  | 7 => 3497 / 500000
  | 8 => 199 / 40000
  | 9 => 737 / 200000
  | 10 => 44 / 15625
  | 11 => 2209 / 1000000
  | 12 => 1769 / 1000000
  | 13 => 1443 / 1000000
  | 14 => 597 / 500000
  | 15 => 501 / 500000
  | 16 => 17 / 20000
  | _ => 0

theorem backlund_right_cell07_scalar :
    Real.log (backlundDirichletEnvelope 16 (1594 / 625 : ℝ)) ≤ 7 / 25 := by
  have h := backlund_right_cell_log_certificate
    (a := 1594 / 625) (l := 7 / 25) (v := 132311 / 100000)
    (qt := 21493 / 5000) (ut := 2191 / 250000) rightCell07Q rightCell07U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell07Q, rightCell07U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell07U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell07 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 7 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      7 / 25 := by
  have ha := backlund_right_cell_sigma (j := 7) (a := 1594 / 625) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (1594 / 625 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell07_scalar

#print axioms backlund_right_cell07_scalar
#print axioms backlund_right_cell07

end LiuWang.Proof.Campaign20260915.RosserCount
