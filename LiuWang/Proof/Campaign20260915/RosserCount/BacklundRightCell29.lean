import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell29Q : ℕ → ℚ
  | 2 => 1559 / 1000
  | 3 => 24711 / 10000
  | 4 => 31181 / 10000
  | 5 => 36201 / 10000
  | 6 => 20151 / 5000
  | 7 => 43769 / 10000
  | 8 => 11693 / 2500
  | 9 => 24711 / 5000
  | 10 => 3237 / 625
  | 11 => 10787 / 2000
  | 12 => 13973 / 2500
  | 13 => 57693 / 10000
  | 14 => 742 / 125
  | 15 => 3807 / 625
  | 16 => 62363 / 10000
  | _ => 0

private def rightCell29U : ℕ → ℚ
  | 1 => 1
  | 2 => 210347 / 1000000
  | 3 => 21123 / 250000
  | 4 => 22121 / 500000
  | 5 => 1339 / 50000
  | 6 => 17771 / 1000000
  | 7 => 2513 / 200000
  | 8 => 4653 / 500000
  | 9 => 7139 / 1000000
  | 10 => 5633 / 1000000
  | 11 => 4547 / 1000000
  | 12 => 3739 / 1000000
  | 13 => 1561 / 500000
  | 14 => 2643 / 1000000
  | 15 => 2263 / 1000000
  | 16 => 979 / 500000
  | _ => 0

theorem backlund_right_cell29_scalar :
    Real.log (backlundDirichletEnvelope 16 (22493 / 10000 : ℝ)) ≤ 949 / 2500 := by
  have h := backlund_right_cell_log_certificate
    (a := 22493 / 10000) (l := 949 / 2500) (v := 365403 / 250000)
    (qt := 34637 / 10000) (ut := 5013 / 200000) rightCell29Q rightCell29U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell29Q, rightCell29U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell29U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell29 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 29 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      949 / 2500 := by
  have ha := backlund_right_cell_sigma (j := 29) (a := 22493 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (22493 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell29_scalar

#print axioms backlund_right_cell29_scalar
#print axioms backlund_right_cell29

end LiuWang.Proof.Campaign20260915.RosserCount
