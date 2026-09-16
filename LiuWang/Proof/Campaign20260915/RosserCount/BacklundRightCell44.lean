import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell44Q : ℕ → ℚ
  | 2 => 811 / 625
  | 3 => 20567 / 10000
  | 4 => 1622 / 625
  | 5 => 3013 / 1000
  | 6 => 33543 / 10000
  | 7 => 36429 / 10000
  | 8 => 38929 / 10000
  | 9 => 20567 / 5000
  | 10 => 21553 / 5000
  | 11 => 4489 / 1000
  | 12 => 46519 / 10000
  | 13 => 24009 / 5000
  | 14 => 9881 / 2000
  | 15 => 50697 / 10000
  | 16 => 10381 / 2000
  | _ => 0

private def rightCell44U : ℕ → ℚ
  | 1 => 1
  | 2 => 273187 / 1000000
  | 3 => 31969 / 250000
  | 4 => 74631 / 1000000
  | 5 => 9829 / 200000
  | 6 => 17467 / 500000
  | 7 => 26177 / 1000000
  | 8 => 20387 / 1000000
  | 9 => 16353 / 1000000
  | 10 => 6713 / 500000
  | 11 => 351 / 31250
  | 12 => 1193 / 125000
  | 13 => 1643 / 200000
  | 14 => 447 / 62500
  | 15 => 1257 / 200000
  | 16 => 557 / 100000
  | _ => 0

theorem backlund_right_cell44_scalar :
    Real.log (backlundDirichletEnvelope 16 (18721 / 10000 : ℝ)) ≤ 2901 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 18721 / 10000) (l := 2901 / 5000) (v := 1786291 / 1000000)
    (qt := 24179 / 10000) (ut := 102177 / 1000000) rightCell44Q rightCell44U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell44Q, rightCell44U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell44U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell44 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 44 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2901 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 44) (a := 18721 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (18721 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell44_scalar

#print axioms backlund_right_cell44_scalar
#print axioms backlund_right_cell44

end LiuWang.Proof.Campaign20260915.RosserCount
