import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell05Q : ℕ → ℚ
  | 2 => 17743 / 10000
  | 3 => 28123 / 10000
  | 4 => 35487 / 10000
  | 5 => 41199 / 10000
  | 6 => 45867 / 10000
  | 7 => 49813 / 10000
  | 8 => 53231 / 10000
  | 9 => 28123 / 5000
  | 10 => 58943 / 10000
  | 11 => 61383 / 10000
  | 12 => 63611 / 10000
  | 13 => 3283 / 500
  | 14 => 67557 / 10000
  | 15 => 69323 / 10000
  | 16 => 2839 / 400
  | _ => 0

private def rightCell05U : ℕ → ℚ
  | 1 => 1
  | 2 => 169603 / 1000000
  | 3 => 60067 / 1000000
  | 4 => 28763 / 1000000
  | 5 => 16247 / 1000000
  | 6 => 10187 / 1000000
  | 7 => 3433 / 500000
  | 8 => 2439 / 500000
  | 9 => 3609 / 1000000
  | 10 => 689 / 250000
  | 11 => 2159 / 1000000
  | 12 => 27 / 15625
  | 13 => 22 / 15625
  | 14 => 233 / 200000
  | 15 => 61 / 62500
  | 16 => 207 / 250000
  | _ => 0

theorem backlund_right_cell05_scalar :
    Real.log (backlundDirichletEnvelope 16 (25599 / 10000 : ℝ)) ≤ 111 / 400 := by
  have h := backlund_right_cell_log_certificate
    (a := 25599 / 10000) (l := 111 / 400) (v := 52789 / 40000)
    (qt := 43249 / 10000) (ut := 1697 / 200000) rightCell05Q rightCell05U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell05Q, rightCell05U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell05U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell05 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 5 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      111 / 400 := by
  have ha := backlund_right_cell_sigma (j := 5) (a := 25599 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (25599 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell05_scalar

#print axioms backlund_right_cell05_scalar
#print axioms backlund_right_cell05

end LiuWang.Proof.Campaign20260915.RosserCount
