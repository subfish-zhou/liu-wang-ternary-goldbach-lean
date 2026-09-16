import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell47Q : ℕ → ℚ
  | 2 => 12371 / 10000
  | 3 => 2451 / 1250
  | 4 => 12371 / 5000
  | 5 => 1149 / 400
  | 6 => 31979 / 10000
  | 7 => 3473 / 1000
  | 8 => 37113 / 10000
  | 9 => 2451 / 625
  | 10 => 5137 / 1250
  | 11 => 42797 / 10000
  | 12 => 887 / 200
  | 13 => 45779 / 10000
  | 14 => 47101 / 10000
  | 15 => 48333 / 10000
  | 16 => 9897 / 2000
  | _ => 0

private def rightCell47U : ℕ → ℚ
  | 1 => 1
  | 2 => 11609 / 40000
  | 3 => 70373 / 500000
  | 4 => 84231 / 1000000
  | 5 => 28279 / 500000
  | 6 => 2553 / 62500
  | 7 => 1939 / 62500
  | 8 => 12223 / 500000
  | 9 => 1981 / 100000
  | 10 => 3283 / 200000
  | 11 => 13847 / 1000000
  | 12 => 741 / 62500
  | 13 => 10277 / 1000000
  | 14 => 2251 / 250000
  | 15 => 7961 / 1000000
  | 16 => 1419 / 200000
  | _ => 0

theorem backlund_right_cell47_scalar :
    Real.log (backlundDirichletEnvelope 16 (2231 / 1250 : ℝ)) ≤ 3233 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 2231 / 1250) (l := 3233 / 5000) (v := 954487 / 500000)
    (qt := 21759 / 10000) (ut := 144631 / 1000000) rightCell47Q rightCell47U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell47Q, rightCell47U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell47U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell47 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 47 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3233 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 47) (a := 2231 / 1250) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2231 / 1250 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell47_scalar

#print axioms backlund_right_cell47_scalar
#print axioms backlund_right_cell47

end LiuWang.Proof.Campaign20260915.RosserCount
