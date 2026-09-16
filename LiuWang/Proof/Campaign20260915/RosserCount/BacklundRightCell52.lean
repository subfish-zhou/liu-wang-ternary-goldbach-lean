import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell52Q : ℕ → ℚ
  | 2 => 11319 / 10000
  | 3 => 897 / 500
  | 4 => 11319 / 5000
  | 5 => 13141 / 5000
  | 6 => 29259 / 10000
  | 7 => 1986 / 625
  | 8 => 33957 / 10000
  | 9 => 897 / 250
  | 10 => 37601 / 10000
  | 11 => 39157 / 10000
  | 12 => 20289 / 5000
  | 13 => 8377 / 2000
  | 14 => 8619 / 2000
  | 15 => 22111 / 5000
  | 16 => 11319 / 2500
  | _ => 0

private def rightCell52U : ℕ → ℚ
  | 1 => 1
  | 2 => 322421 / 1000000
  | 3 => 83147 / 500000
  | 4 => 20791 / 200000
  | 5 => 72209 / 1000000
  | 6 => 53617 / 1000000
  | 7 => 20843 / 500000
  | 8 => 16759 / 500000
  | 9 => 13827 / 500000
  | 10 => 11641 / 500000
  | 11 => 19927 / 1000000
  | 12 => 2161 / 125000
  | 13 => 1517 / 100000
  | 14 => 13441 / 1000000
  | 15 => 1501 / 125000
  | 16 => 10807 / 1000000
  | _ => 0

theorem backlund_right_cell52_scalar :
    Real.log (backlundDirichletEnvelope 16 (1633 / 1000 : ℝ)) ≤ 3957 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 1633 / 1000) (l := 3957 / 5000) (v := 2206433 / 1000000)
    (qt := 351 / 200) (ut := 68289 / 250000) rightCell52Q rightCell52U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell52Q, rightCell52U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell52U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell52 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 52 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3957 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 52) (a := 1633 / 1000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (1633 / 1000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell52_scalar

#print axioms backlund_right_cell52_scalar
#print axioms backlund_right_cell52

end LiuWang.Proof.Campaign20260915.RosserCount
