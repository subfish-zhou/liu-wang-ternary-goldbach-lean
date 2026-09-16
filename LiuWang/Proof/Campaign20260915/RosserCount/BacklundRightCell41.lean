import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell41Q : ℕ → ℚ
  | 2 => 13557 / 10000
  | 3 => 1343 / 625
  | 4 => 5423 / 2000
  | 5 => 787 / 250
  | 6 => 17523 / 5000
  | 7 => 38061 / 10000
  | 8 => 40673 / 10000
  | 9 => 42977 / 10000
  | 10 => 22519 / 5000
  | 11 => 23451 / 5000
  | 12 => 12151 / 2500
  | 13 => 5017 / 1000
  | 14 => 51619 / 10000
  | 15 => 52969 / 10000
  | 16 => 54231 / 10000
  | _ => 0

private def rightCell41U : ℕ → ℚ
  | 1 => 1
  | 2 => 257767 / 1000000
  | 3 => 933 / 8000
  | 4 => 33219 / 500000
  | 5 => 21469 / 500000
  | 6 => 30059 / 1000000
  | 7 => 4447 / 200000
  | 8 => 4281 / 250000
  | 9 => 17 / 1250
  | 10 => 11067 / 1000000
  | 11 => 1837 / 200000
  | 12 => 1937 / 250000
  | 13 => 53 / 8000
  | 14 => 5731 / 1000000
  | 15 => 313 / 62500
  | 16 => 2207 / 500000
  | _ => 0

theorem backlund_right_cell41_scalar :
    Real.log (backlundDirichletEnvelope 16 (489 / 250 : ℝ)) ≤ 21 / 40 := by
  have h := backlund_right_cell_log_certificate
    (a := 489 / 250) (l := 21 / 40) (v := 1690431 / 1000000)
    (qt := 5301 / 2000) (ut := 73867 / 1000000) rightCell41Q rightCell41U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell41Q, rightCell41U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell41U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell41 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 41 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      21 / 40 := by
  have ha := backlund_right_cell_sigma (j := 41) (a := 489 / 250) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (489 / 250 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell41_scalar

#print axioms backlund_right_cell41_scalar
#print axioms backlund_right_cell41

end LiuWang.Proof.Campaign20260915.RosserCount
