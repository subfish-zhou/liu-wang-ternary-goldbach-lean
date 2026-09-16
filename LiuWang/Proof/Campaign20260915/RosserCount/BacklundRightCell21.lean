import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell21Q : ℕ → ℚ
  | 2 => 16623 / 10000
  | 3 => 26347 / 10000
  | 4 => 33247 / 10000
  | 5 => 38599 / 10000
  | 6 => 42971 / 10000
  | 7 => 11667 / 2500
  | 8 => 49871 / 10000
  | 9 => 6587 / 1250
  | 10 => 27611 / 5000
  | 11 => 14377 / 2500
  | 12 => 11919 / 2000
  | 13 => 12303 / 2000
  | 14 => 15823 / 2500
  | 15 => 64947 / 10000
  | 16 => 33247 / 5000
  | _ => 0

private def rightCell21U : ℕ → ℚ
  | 1 => 1
  | 2 => 189703 / 1000000
  | 3 => 71741 / 1000000
  | 4 => 2249 / 62500
  | 5 => 21071 / 1000000
  | 6 => 1701 / 125000
  | 7 => 9403 / 1000000
  | 8 => 3413 / 500000
  | 9 => 2573 / 500000
  | 10 => 1999 / 500000
  | 11 => 3181 / 1000000
  | 12 => 1291 / 500000
  | 13 => 2131 / 1000000
  | 14 => 223 / 125000
  | 15 => 189 / 125000
  | 16 => 259 / 200000
  | _ => 0

theorem backlund_right_cell21_scalar :
    Real.log (backlundDirichletEnvelope 16 (23983 / 10000 : ℝ)) ≤ 407 / 1250 := by
  have h := backlund_right_cell_log_certificate
    (a := 23983 / 10000) (l := 407 / 1250) (v := 69239 / 50000)
    (qt := 38769 / 10000) (ut := 2963 / 200000) rightCell21Q rightCell21U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell21Q, rightCell21U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell21U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell21 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 21 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      407 / 1250 := by
  have ha := backlund_right_cell_sigma (j := 21) (a := 23983 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (23983 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell21_scalar

#print axioms backlund_right_cell21_scalar
#print axioms backlund_right_cell21

end LiuWang.Proof.Campaign20260915.RosserCount
