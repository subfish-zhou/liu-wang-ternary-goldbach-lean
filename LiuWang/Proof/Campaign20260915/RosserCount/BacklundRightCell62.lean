import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell62Q : ℕ → ℚ
  | 2 => 1139 / 1250
  | 3 => 7221 / 5000
  | 4 => 1139 / 625
  | 5 => 21157 / 10000
  | 6 => 11777 / 5000
  | 7 => 1279 / 500
  | 8 => 3417 / 1250
  | 9 => 7221 / 2500
  | 10 => 30269 / 10000
  | 11 => 15761 / 5000
  | 12 => 16333 / 5000
  | 13 => 16859 / 5000
  | 14 => 34693 / 10000
  | 15 => 89 / 25
  | 16 => 2278 / 625
  | _ => 0

private def rightCell62U : ℕ → ℚ
  | 1 => 1
  | 2 => 201021 / 500000
  | 3 => 47187 / 200000
  | 4 => 80819 / 500000
  | 5 => 120549 / 1000000
  | 6 => 11857 / 125000
  | 7 => 3873 / 50000
  | 8 => 12997 / 200000
  | 9 => 27833 / 500000
  | 10 => 24233 / 500000
  | 11 => 21379 / 500000
  | 12 => 4767 / 125000
  | 13 => 4291 / 125000
  | 14 => 31139 / 1000000
  | 15 => 28439 / 1000000
  | 16 => 26127 / 1000000
  | _ => 0

theorem backlund_right_cell62_scalar :
    Real.log (backlundDirichletEnvelope 16 (6573 / 5000 : ℝ)) ≤ 833 / 625 := by
  have h := backlund_right_cell_log_certificate
    (a := 6573 / 5000) (l := 833 / 625) (v := 1895647 / 500000)
    (qt := 4361 / 5000) (ut := 132877 / 100000) rightCell62Q rightCell62U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell62Q, rightCell62U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell62U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell62 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 62 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      833 / 625 := by
  have ha := backlund_right_cell_sigma (j := 62) (a := 6573 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (6573 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell62_scalar

#print axioms backlund_right_cell62_scalar
#print axioms backlund_right_cell62

end LiuWang.Proof.Campaign20260915.RosserCount
