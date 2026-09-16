import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell09Q : ℕ → ℚ
  | 2 => 1759 / 1000
  | 3 => 697 / 250
  | 4 => 35181 / 10000
  | 5 => 10211 / 2500
  | 6 => 45471 / 10000
  | 7 => 49383 / 10000
  | 8 => 13193 / 2500
  | 9 => 55761 / 10000
  | 10 => 29217 / 5000
  | 11 => 60853 / 10000
  | 12 => 63061 / 10000
  | 13 => 65093 / 10000
  | 14 => 66973 / 10000
  | 15 => 17181 / 2500
  | 16 => 35181 / 5000
  | _ => 0

private def rightCell09U : ℕ → ℚ
  | 1 => 1
  | 2 => 172217 / 1000000
  | 3 => 12309 / 200000
  | 4 => 3707 / 125000
  | 5 => 8417 / 500000
  | 6 => 5299 / 500000
  | 7 => 7167 / 1000000
  | 8 => 5107 / 1000000
  | 9 => 947 / 250000
  | 10 => 2899 / 1000000
  | 11 => 2277 / 1000000
  | 12 => 913 / 500000
  | 13 => 149 / 100000
  | 14 => 247 / 200000
  | 15 => 259 / 250000
  | 16 => 11 / 12500
  | _ => 0

theorem backlund_right_cell09_scalar :
    Real.log (backlundDirichletEnvelope 16 (12689 / 5000 : ℝ)) ≤ 567 / 2000 := by
  have h := backlund_right_cell_log_certificate
    (a := 12689 / 5000) (l := 567 / 2000) (v := 663853 / 500000)
    (qt := 10659 / 2500) (ut := 9151 / 1000000) rightCell09Q rightCell09U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell09Q, rightCell09U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell09U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell09 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 9 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      567 / 2000 := by
  have ha := backlund_right_cell_sigma (j := 9) (a := 12689 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (12689 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell09_scalar

#print axioms backlund_right_cell09_scalar
#print axioms backlund_right_cell09

end LiuWang.Proof.Campaign20260915.RosserCount
