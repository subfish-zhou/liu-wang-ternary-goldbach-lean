import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell33Q : ℕ → ℚ
  | 2 => 14971 / 10000
  | 3 => 2373 / 1000
  | 4 => 29943 / 10000
  | 5 => 34763 / 10000
  | 6 => 38701 / 10000
  | 7 => 42031 / 10000
  | 8 => 8983 / 2000
  | 9 => 2373 / 500
  | 10 => 9947 / 2000
  | 11 => 25897 / 5000
  | 12 => 53673 / 10000
  | 13 => 27701 / 5000
  | 14 => 57003 / 10000
  | 15 => 58493 / 10000
  | 16 => 59887 / 10000
  | _ => 0

private def rightCell33U : ℕ → ℚ
  | 1 => 1
  | 2 => 223779 / 1000000
  | 3 => 93201 / 1000000
  | 4 => 6259 / 125000
  | 5 => 15461 / 500000
  | 6 => 20857 / 1000000
  | 7 => 299 / 20000
  | 8 => 2801 / 250000
  | 9 => 8687 / 1000000
  | 10 => 6919 / 1000000
  | 11 => 88 / 15625
  | 12 => 4667 / 1000000
  | 13 => 1963 / 500000
  | 14 => 669 / 200000
  | 15 => 1441 / 500000
  | 16 => 2507 / 1000000
  | _ => 0

theorem backlund_right_cell33_scalar :
    Real.log (backlundDirichletEnvelope 16 (54 / 25 : ℝ)) ≤ 167 / 400 := by
  have h := backlund_right_cell_log_certificate
    (a := 54 / 25) (l := 167 / 400) (v := 759063 / 500000)
    (qt := 16081 / 5000) (ut := 2161 / 62500) rightCell33Q rightCell33U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell33Q, rightCell33U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell33U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell33 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 33 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      167 / 400 := by
  have ha := backlund_right_cell_sigma (j := 33) (a := 54 / 25) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (54 / 25 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell33_scalar

#print axioms backlund_right_cell33_scalar
#print axioms backlund_right_cell33

end LiuWang.Proof.Campaign20260915.RosserCount
