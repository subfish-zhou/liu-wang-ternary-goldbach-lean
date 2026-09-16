import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell11Q : ℕ → ℚ
  | 2 => 17481 / 10000
  | 3 => 13853 / 5000
  | 4 => 17481 / 5000
  | 5 => 40589 / 10000
  | 6 => 11297 / 2500
  | 7 => 1963 / 400
  | 8 => 52443 / 10000
  | 9 => 55413 / 10000
  | 10 => 58071 / 10000
  | 11 => 30237 / 5000
  | 12 => 62669 / 10000
  | 13 => 64687 / 10000
  | 14 => 66557 / 10000
  | 15 => 68297 / 10000
  | 16 => 17481 / 2500
  | _ => 0

private def rightCell11U : ℕ → ℚ
  | 1 => 1
  | 2 => 34821 / 200000
  | 3 => 501 / 8000
  | 4 => 30313 / 1000000
  | 5 => 17269 / 1000000
  | 6 => 10903 / 1000000
  | 7 => 7391 / 1000000
  | 8 => 2639 / 500000
  | 9 => 1961 / 500000
  | 10 => 3007 / 1000000
  | 11 => 473 / 200000
  | 12 => 1899 / 1000000
  | 13 => 97 / 62500
  | 14 => 1287 / 1000000
  | 15 => 541 / 500000
  | 16 => 919 / 1000000
  | _ => 0

theorem backlund_right_cell11_scalar :
    Real.log (backlundDirichletEnvelope 16 (1261 / 500 : ℝ)) ≤ 2879 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 1261 / 500) (l := 2879 / 10000) (v := 1333577 / 1000000)
    (qt := 21099 / 5000) (ut := 483 / 50000) rightCell11Q rightCell11U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell11Q, rightCell11U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell11U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell11 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 11 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      2879 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 11) (a := 1261 / 500) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (1261 / 500 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell11_scalar

#print axioms backlund_right_cell11_scalar
#print axioms backlund_right_cell11

end LiuWang.Proof.Campaign20260915.RosserCount
