import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell39Q : ℕ → ℚ
  | 2 => 13931 / 10000
  | 3 => 276 / 125
  | 4 => 27863 / 10000
  | 5 => 8087 / 2500
  | 6 => 9003 / 2500
  | 7 => 3911 / 1000
  | 8 => 20897 / 5000
  | 9 => 44161 / 10000
  | 10 => 46279 / 10000
  | 11 => 9639 / 2000
  | 12 => 6243 / 1250
  | 13 => 3222 / 625
  | 14 => 26521 / 5000
  | 15 => 54429 / 10000
  | 16 => 27863 / 5000
  | _ => 0

private def rightCell39U : ℕ → ℚ
  | 1 => 1
  | 2 => 49661 / 200000
  | 3 => 109921 / 1000000
  | 4 => 61649 / 1000000
  | 5 => 39369 / 1000000
  | 6 => 27291 / 1000000
  | 7 => 20021 / 1000000
  | 8 => 3827 / 250000
  | 9 => 6041 / 500000
  | 10 => 611 / 62500
  | 11 => 8071 / 1000000
  | 12 => 847 / 125000
  | 13 => 577 / 100000
  | 14 => 4971 / 1000000
  | 15 => 4327 / 1000000
  | 16 => 3801 / 1000000
  | _ => 0

theorem backlund_right_cell39_scalar :
    Real.log (backlundDirichletEnvelope 16 (20099 / 10000 : ℝ)) ≤ 4933 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 20099 / 10000) (l := 4933 / 10000) (v := 409413 / 250000)
    (qt := 14 / 5) (ut := 30107 / 500000) rightCell39Q rightCell39U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell39Q, rightCell39U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell39U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell39 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 39 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      4933 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 39) (a := 20099 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (20099 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell39_scalar

#print axioms backlund_right_cell39_scalar
#print axioms backlund_right_cell39

end LiuWang.Proof.Campaign20260915.RosserCount
