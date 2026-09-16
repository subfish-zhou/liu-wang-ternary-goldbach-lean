import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell63Q : ℕ → ℚ
  | 2 => 8887 / 10000
  | 3 => 7043 / 5000
  | 4 => 711 / 400
  | 5 => 5159 / 2500
  | 6 => 22973 / 10000
  | 7 => 499 / 200
  | 8 => 13331 / 5000
  | 9 => 7043 / 2500
  | 10 => 29523 / 10000
  | 11 => 6149 / 2000
  | 12 => 31861 / 10000
  | 13 => 32887 / 10000
  | 14 => 33837 / 10000
  | 15 => 17361 / 5000
  | 16 => 711 / 200
  | _ => 0

private def rightCell63U : ℕ → ℚ
  | 1 => 1
  | 2 => 41119 / 100000
  | 3 => 122243 / 500000
  | 4 => 169061 / 1000000
  | 5 => 31749 / 250000
  | 6 => 10053 / 100000
  | 7 => 82497 / 1000000
  | 8 => 17379 / 250000
  | 9 => 29887 / 500000
  | 10 => 2611 / 50000
  | 11 => 46213 / 1000000
  | 12 => 41333 / 1000000
  | 13 => 37303 / 1000000
  | 14 => 16961 / 500000
  | 15 => 31049 / 1000000
  | 16 => 14291 / 500000
  | _ => 0

theorem backlund_right_cell63_scalar :
    Real.log (backlundDirichletEnvelope 16 (6411 / 5000 : ℝ)) ≤ 3561 / 2500 := by
  have h := backlund_right_cell_log_certificate
    (a := 6411 / 5000) (l := 3561 / 2500) (v := 207759 / 50000)
    (qt := 489 / 625) (ut := 405127 / 250000) rightCell63Q rightCell63U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell63Q, rightCell63U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell63U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell63 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 63 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3561 / 2500 := by
  have ha := backlund_right_cell_sigma (j := 63) (a := 6411 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (6411 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell63_scalar

#print axioms backlund_right_cell63_scalar
#print axioms backlund_right_cell63

end LiuWang.Proof.Campaign20260915.RosserCount
