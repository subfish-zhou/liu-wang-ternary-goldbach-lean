import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell38Q : ℕ → ℚ
  | 2 => 14113 / 10000
  | 3 => 22369 / 10000
  | 4 => 28227 / 10000
  | 5 => 32771 / 10000
  | 6 => 36483 / 10000
  | 7 => 19811 / 5000
  | 8 => 42341 / 10000
  | 9 => 44739 / 10000
  | 10 => 9377 / 2000
  | 11 => 1953 / 400
  | 12 => 50597 / 10000
  | 13 => 52227 / 10000
  | 14 => 6717 / 1250
  | 15 => 55141 / 10000
  | 16 => 11291 / 2000
  | _ => 0

private def rightCell38U : ℕ → ℚ
  | 1 => 1
  | 2 => 243827 / 1000000
  | 3 => 10679 / 100000
  | 4 => 29723 / 500000
  | 5 => 18869 / 500000
  | 6 => 6509 / 250000
  | 7 => 9511 / 500000
  | 8 => 14493 / 1000000
  | 9 => 11403 / 1000000
  | 10 => 9201 / 1000000
  | 11 => 7579 / 1000000
  | 12 => 1587 / 250000
  | 13 => 5393 / 1000000
  | 14 => 2319 / 500000
  | 15 => 403 / 100000
  | 16 => 1767 / 500000
  | _ => 0

theorem backlund_right_cell38_scalar :
    Real.log (backlundDirichletEnvelope 16 (10181 / 5000 : ℝ)) ≤ 1197 / 2500 := by
  have h := backlund_right_cell_log_certificate
    (a := 10181 / 5000) (l := 1197 / 2500) (v := 807019 / 500000)
    (qt := 28729 / 10000) (ut := 341 / 6250) rightCell38Q rightCell38U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell38Q, rightCell38U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell38U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell38 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 38 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      1197 / 2500 := by
  have ha := backlund_right_cell_sigma (j := 38) (a := 10181 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (10181 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell38_scalar

#print axioms backlund_right_cell38_scalar
#print axioms backlund_right_cell38

end LiuWang.Proof.Campaign20260915.RosserCount
