import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell12Q : ℕ → ℚ
  | 2 => 8709 / 5000
  | 3 => 3451 / 1250
  | 4 => 34837 / 10000
  | 5 => 8089 / 2000
  | 6 => 22513 / 5000
  | 7 => 489 / 100
  | 8 => 3266 / 625
  | 9 => 3451 / 625
  | 10 => 57863 / 10000
  | 11 => 60259 / 10000
  | 12 => 12489 / 2000
  | 13 => 64457 / 10000
  | 14 => 66319 / 10000
  | 15 => 68053 / 10000
  | 16 => 2787 / 400
  | _ => 0

private def rightCell12U : ℕ → ℚ
  | 1 => 1
  | 2 => 35041 / 200000
  | 3 => 31621 / 500000
  | 4 => 15347 / 500000
  | 5 => 17519 / 1000000
  | 6 => 11081 / 1000000
  | 7 => 3761 / 500000
  | 8 => 2689 / 500000
  | 9 => 1 / 250
  | 10 => 307 / 100000
  | 11 => 151 / 62500
  | 12 => 971 / 500000
  | 13 => 397 / 250000
  | 14 => 659 / 500000
  | 15 => 277 / 250000
  | 16 => 943 / 1000000
  | _ => 0

theorem backlund_right_cell12_scalar :
    Real.log (backlundDirichletEnvelope 16 (2513 / 1000 : ℝ)) ≤ 581 / 2000 := by
  have h := backlund_right_cell_log_certificate
    (a := 2513 / 1000) (l := 581 / 2000) (v := 334247 / 250000)
    (qt := 41949 / 10000) (ut := 4981 / 500000) rightCell12Q rightCell12U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell12Q, rightCell12U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell12U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell12 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 12 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      581 / 2000 := by
  have ha := backlund_right_cell_sigma (j := 12) (a := 2513 / 1000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2513 / 1000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell12_scalar

#print axioms backlund_right_cell12_scalar
#print axioms backlund_right_cell12

end LiuWang.Proof.Campaign20260915.RosserCount
