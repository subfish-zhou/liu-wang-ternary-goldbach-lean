import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell43Q : ℕ → ℚ
  | 2 => 13173 / 10000
  | 3 => 20879 / 10000
  | 4 => 13173 / 5000
  | 5 => 30587 / 10000
  | 6 => 8513 / 2500
  | 7 => 18491 / 5000
  | 8 => 39519 / 10000
  | 9 => 20879 / 5000
  | 10 => 547 / 125
  | 11 => 45571 / 10000
  | 12 => 1889 / 400
  | 13 => 24373 / 5000
  | 14 => 10031 / 2000
  | 15 => 25733 / 5000
  | 16 => 52693 / 10000
  | _ => 0

private def rightCell43U : ℕ → ℚ
  | 1 => 1
  | 2 => 133929 / 500000
  | 3 => 30987 / 250000
  | 4 => 17937 / 250000
  | 5 => 46949 / 1000000
  | 6 => 33201 / 1000000
  | 7 => 24769 / 1000000
  | 8 => 19219 / 1000000
  | 9 => 15363 / 1000000
  | 10 => 393 / 31250
  | 11 => 10493 / 1000000
  | 12 => 8893 / 1000000
  | 13 => 7639 / 1000000
  | 14 => 1327 / 200000
  | 15 => 291 / 50000
  | 16 => 1287 / 250000
  | _ => 0

theorem backlund_right_cell43_scalar :
    Real.log (backlundDirichletEnvelope 16 (3801 / 2000 : ℝ)) ≤ 2803 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 3801 / 2000) (l := 2803 / 5000) (v := 437929 / 250000)
    (qt := 24967 / 10000) (ut := 91457 / 1000000) rightCell43Q rightCell43U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell43Q, rightCell43U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell43U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell43 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 43 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2803 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 43) (a := 3801 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (3801 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell43_scalar

#print axioms backlund_right_cell43_scalar
#print axioms backlund_right_cell43

end LiuWang.Proof.Campaign20260915.RosserCount
