import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell26Q : ℕ → ℚ
  | 2 => 4003 / 2500
  | 3 => 25379 / 10000
  | 4 => 4003 / 1250
  | 5 => 37179 / 10000
  | 6 => 41391 / 10000
  | 7 => 5619 / 1250
  | 8 => 48037 / 10000
  | 9 => 25379 / 5000
  | 10 => 53191 / 10000
  | 11 => 55393 / 10000
  | 12 => 57403 / 10000
  | 13 => 14813 / 2500
  | 14 => 15241 / 2500
  | 15 => 31279 / 5000
  | 16 => 64049 / 10000
  | _ => 0

private def rightCell26U : ℕ → ℚ
  | 1 => 1
  | 2 => 40331 / 200000
  | 3 => 79033 / 1000000
  | 4 => 8133 / 200000
  | 5 => 4857 / 200000
  | 6 => 7969 / 500000
  | 7 => 11163 / 1000000
  | 8 => 41 / 5000
  | 9 => 6247 / 1000000
  | 10 => 2449 / 500000
  | 11 => 393 / 100000
  | 12 => 1607 / 500000
  | 13 => 167 / 62500
  | 14 => 2251 / 1000000
  | 15 => 6 / 3125
  | 16 => 827 / 500000
  | _ => 0

theorem backlund_right_cell26_scalar :
    Real.log (backlundDirichletEnvelope 16 (23101 / 10000 : ℝ)) ≤ 3563 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 23101 / 10000) (l := 3563 / 10000) (v := 1427919 / 1000000)
    (qt := 36323 / 10000) (ut := 10097 / 500000) rightCell26Q rightCell26U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell26Q, rightCell26U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell26U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell26 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 26 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3563 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 26) (a := 23101 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (23101 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell26_scalar

#print axioms backlund_right_cell26_scalar
#print axioms backlund_right_cell26

end LiuWang.Proof.Campaign20260915.RosserCount
