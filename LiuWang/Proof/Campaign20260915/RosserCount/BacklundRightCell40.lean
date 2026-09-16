import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell40Q : ℕ → ℚ
  | 2 => 6873 / 5000
  | 3 => 21787 / 10000
  | 4 => 6873 / 2500
  | 5 => 15959 / 5000
  | 6 => 17767 / 5000
  | 7 => 38591 / 10000
  | 8 => 41239 / 10000
  | 9 => 1743 / 400
  | 10 => 2854 / 625
  | 11 => 9511 / 2000
  | 12 => 616 / 125
  | 13 => 12717 / 2500
  | 14 => 52337 / 10000
  | 15 => 26853 / 5000
  | 16 => 10997 / 2000
  | _ => 0

private def rightCell40U : ℕ → ℚ
  | 1 => 1
  | 2 => 252941 / 1000000
  | 3 => 113189 / 1000000
  | 4 => 3199 / 50000
  | 5 => 20549 / 500000
  | 6 => 7157 / 250000
  | 7 => 21087 / 1000000
  | 8 => 8091 / 500000
  | 9 => 12811 / 1000000
  | 10 => 2599 / 250000
  | 11 => 1721 / 200000
  | 12 => 7241 / 1000000
  | 13 => 3089 / 500000
  | 14 => 2667 / 500000
  | 15 => 1163 / 250000
  | 16 => 4093 / 1000000
  | _ => 0

theorem backlund_right_cell40_scalar :
    Real.log (backlundDirichletEnvelope 16 (2479 / 1250 : ℝ)) ≤ 5087 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 2479 / 1250) (l := 5087 / 10000) (v := 332603 / 200000)
    (qt := 1363 / 500) (ut := 333 / 5000) rightCell40Q rightCell40U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell40Q, rightCell40U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell40U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell40 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 40 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      5087 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 40) (a := 2479 / 1250) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2479 / 1250 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell40_scalar

#print axioms backlund_right_cell40_scalar
#print axioms backlund_right_cell40

end LiuWang.Proof.Campaign20260915.RosserCount
