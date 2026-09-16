import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell01Q : ℕ → ℚ
  | 2 => 17809 / 10000
  | 3 => 28227 / 10000
  | 4 => 35619 / 10000
  | 5 => 5169 / 1250
  | 6 => 46037 / 10000
  | 7 => 24999 / 5000
  | 8 => 53429 / 10000
  | 9 => 11291 / 2000
  | 10 => 29581 / 5000
  | 11 => 61611 / 10000
  | 12 => 63847 / 10000
  | 13 => 65903 / 10000
  | 14 => 67807 / 10000
  | 15 => 3479 / 500
  | 16 => 35619 / 5000
  | _ => 0

private def rightCell01U : ℕ → ℚ
  | 1 => 1
  | 2 => 168487 / 1000000
  | 3 => 29723 / 500000
  | 4 => 5677 / 200000
  | 5 => 2 / 125
  | 6 => 2003 / 200000
  | 7 => 337 / 50000
  | 8 => 2391 / 500000
  | 9 => 1767 / 500000
  | 10 => 337 / 125000
  | 11 => 211 / 100000
  | 12 => 211 / 125000
  | 13 => 687 / 500000
  | 14 => 71 / 62500
  | 15 => 951 / 1000000
  | 16 => 403 / 500000
  | _ => 0

theorem backlund_right_cell01_scalar :
    Real.log (backlundDirichletEnvelope 16 (12847 / 5000 : ℝ)) ≤ 2749 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 12847 / 5000) (l := 2749 / 10000) (v := 263273 / 200000)
    (qt := 5439 / 1250) (ut := 1643 / 200000) rightCell01Q rightCell01U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell01Q, rightCell01U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell01U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell01 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 1 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2749 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 1) (a := 12847 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (12847 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell01_scalar

#print axioms backlund_right_cell01_scalar
#print axioms backlund_right_cell01

end LiuWang.Proof.Campaign20260915.RosserCount
