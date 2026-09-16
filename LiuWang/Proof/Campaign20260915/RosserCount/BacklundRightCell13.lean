import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell13Q : ℕ → ℚ
  | 2 => 347 / 200
  | 3 => 11 / 4
  | 4 => 34701 / 10000
  | 5 => 40287 / 10000
  | 6 => 44851 / 10000
  | 7 => 48709 / 10000
  | 8 => 13013 / 2500
  | 9 => 11 / 2
  | 10 => 28819 / 5000
  | 11 => 7503 / 1250
  | 12 => 31101 / 5000
  | 13 => 12841 / 2000
  | 14 => 3303 / 500
  | 15 => 67787 / 10000
  | 16 => 69403 / 10000
  | _ => 0

private def rightCell13U : ℕ → ℚ
  | 1 => 1
  | 2 => 176401 / 1000000
  | 3 => 7991 / 125000
  | 4 => 15557 / 500000
  | 5 => 8899 / 500000
  | 6 => 2819 / 250000
  | 7 => 7667 / 1000000
  | 8 => 343 / 62500
  | 9 => 4087 / 1000000
  | 10 => 157 / 50000
  | 11 => 2473 / 1000000
  | 12 => 1989 / 1000000
  | 13 => 407 / 250000
  | 14 => 1353 / 1000000
  | 15 => 569 / 500000
  | 16 => 121 / 125000
  | _ => 0

theorem backlund_right_cell13_scalar :
    Real.log (backlundDirichletEnvelope 16 (3129 / 1250 : ℝ)) ≤ 2933 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 3129 / 1250) (l := 2933 / 10000) (v := 83797 / 62500)
    (qt := 41677 / 10000) (ut := 161 / 15625) rightCell13Q rightCell13U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell13Q, rightCell13U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell13U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell13 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 13 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2933 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 13) (a := 3129 / 1250) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (3129 / 1250 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell13_scalar

#print axioms backlund_right_cell13_scalar
#print axioms backlund_right_cell13

end LiuWang.Proof.Campaign20260915.RosserCount
