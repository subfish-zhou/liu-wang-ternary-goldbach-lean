import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell17Q : ℕ → ℚ
  | 2 => 17027 / 10000
  | 3 => 6747 / 2500
  | 4 => 6811 / 2000
  | 5 => 39537 / 10000
  | 6 => 2751 / 625
  | 7 => 47803 / 10000
  | 8 => 51083 / 10000
  | 9 => 6747 / 1250
  | 10 => 11313 / 2000
  | 11 => 29453 / 5000
  | 12 => 15261 / 2500
  | 13 => 6301 / 1000
  | 14 => 64831 / 10000
  | 15 => 2661 / 400
  | 16 => 68111 / 10000
  | _ => 0

private def rightCell17U : ℕ → ℚ
  | 1 => 1
  | 2 => 182191 / 1000000
  | 3 => 67287 / 1000000
  | 4 => 33191 / 1000000
  | 5 => 1199 / 62500
  | 6 => 6129 / 500000
  | 7 => 4197 / 500000
  | 8 => 6047 / 1000000
  | 9 => 283 / 62500
  | 10 => 699 / 200000
  | 11 => 1383 / 500000
  | 12 => 1117 / 500000
  | 13 => 367 / 200000
  | 14 => 153 / 100000
  | 15 => 1291 / 1000000
  | 16 => 551 / 500000
  | _ => 0

theorem backlund_right_cell17_scalar :
    Real.log (backlundDirichletEnvelope 16 (12283 / 5000 : ℝ)) ≤ 3071 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 12283 / 5000) (l := 3071 / 10000) (v := 1359433 / 1000000)
    (qt := 8077 / 2000) (ut := 121 / 10000) rightCell17Q rightCell17U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell17Q, rightCell17U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell17U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell17 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 17 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3071 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 17) (a := 12283 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (12283 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell17_scalar

#print axioms backlund_right_cell17_scalar
#print axioms backlund_right_cell17

end LiuWang.Proof.Campaign20260915.RosserCount
