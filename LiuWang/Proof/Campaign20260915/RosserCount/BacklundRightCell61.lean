import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell61Q : ℕ → ℚ
  | 2 => 1867 / 2000
  | 3 => 14797 / 10000
  | 4 => 18671 / 10000
  | 5 => 21677 / 10000
  | 6 => 24133 / 10000
  | 7 => 26209 / 10000
  | 8 => 28007 / 10000
  | 9 => 14797 / 5000
  | 10 => 31013 / 10000
  | 11 => 32297 / 10000
  | 12 => 33469 / 10000
  | 13 => 34547 / 10000
  | 14 => 7109 / 2000
  | 15 => 18237 / 5000
  | 16 => 37343 / 10000
  | _ => 0

private def rightCell61U : ℕ → ℚ
  | 1 => 1
  | 2 => 49147 / 125000
  | 3 => 113853 / 500000
  | 4 => 38643 / 250000
  | 5 => 114441 / 1000000
  | 6 => 1119 / 12500
  | 7 => 36369 / 500000
  | 8 => 1899 / 31250
  | 9 => 51851 / 1000000
  | 10 => 44991 / 1000000
  | 11 => 3957 / 100000
  | 12 => 17597 / 500000
  | 13 => 31597 / 1000000
  | 14 => 7149 / 250000
  | 15 => 26059 / 1000000
  | 16 => 2389 / 100000
  | _ => 0

theorem backlund_right_cell61_scalar :
    Real.log (backlundDirichletEnvelope 16 (13469 / 10000 : ℝ)) ≤ 6259 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 13469 / 10000) (l := 6259 / 5000) (v := 87411 / 25000)
    (qt := 4809 / 5000) (ut := 1101771 / 1000000) rightCell61Q rightCell61U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell61Q, rightCell61U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell61U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell61 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 61 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      6259 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 61) (a := 13469 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (13469 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell61_scalar

#print axioms backlund_right_cell61_scalar
#print axioms backlund_right_cell61

end LiuWang.Proof.Campaign20260915.RosserCount
