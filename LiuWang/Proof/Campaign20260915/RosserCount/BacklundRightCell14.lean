import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell14Q : ℕ → ℚ
  | 2 => 8639 / 5000
  | 3 => 5477 / 2000
  | 4 => 8639 / 2500
  | 5 => 20059 / 5000
  | 6 => 44663 / 10000
  | 7 => 9701 / 2000
  | 8 => 25917 / 5000
  | 9 => 5477 / 1000
  | 10 => 14349 / 2500
  | 11 => 14943 / 2500
  | 12 => 61941 / 10000
  | 13 => 3996 / 625
  | 14 => 65783 / 10000
  | 15 => 67503 / 10000
  | 16 => 8639 / 1250
  | _ => 0

private def rightCell14U : ℕ → ℚ
  | 1 => 1
  | 2 => 7107 / 40000
  | 3 => 16167 / 250000
  | 4 => 31569 / 1000000
  | 5 => 18101 / 1000000
  | 6 => 1149 / 100000
  | 7 => 313 / 40000
  | 8 => 5609 / 1000000
  | 9 => 2091 / 500000
  | 10 => 3217 / 1000000
  | 11 => 317 / 125000
  | 12 => 1021 / 500000
  | 13 => 1673 / 1000000
  | 14 => 1391 / 1000000
  | 15 => 1171 / 1000000
  | 16 => 997 / 1000000
  | _ => 0

theorem backlund_right_cell14_scalar :
    Real.log (backlundDirichletEnvelope 16 (24927 / 10000 : ℝ)) ≤ 2963 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 24927 / 10000) (l := 2963 / 10000) (v := 1344829 / 1000000)
    (qt := 20693 / 5000) (ut := 10683 / 1000000) rightCell14Q rightCell14U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell14Q, rightCell14U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell14U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell14 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 14 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2963 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 14) (a := 24927 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (24927 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell14_scalar

#print axioms backlund_right_cell14_scalar
#print axioms backlund_right_cell14

end LiuWang.Proof.Campaign20260915.RosserCount
