import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell20Q : ℕ → ℚ
  | 2 => 4183 / 2500
  | 3 => 663 / 250
  | 4 => 6693 / 2000
  | 5 => 38851 / 10000
  | 6 => 43253 / 10000
  | 7 => 23487 / 5000
  | 8 => 50197 / 10000
  | 9 => 663 / 125
  | 10 => 3474 / 625
  | 11 => 11577 / 2000
  | 12 => 11997 / 2000
  | 13 => 61917 / 10000
  | 14 => 31853 / 5000
  | 15 => 16343 / 2500
  | 16 => 6693 / 1000
  | _ => 0

private def rightCell20U : ℕ → ℚ
  | 1 => 1
  | 2 => 93823 / 500000
  | 3 => 70511 / 1000000
  | 4 => 4401 / 125000
  | 5 => 10273 / 500000
  | 6 => 1323 / 100000
  | 7 => 9119 / 1000000
  | 8 => 6607 / 1000000
  | 9 => 1243 / 250000
  | 10 => 771 / 200000
  | 11 => 3063 / 1000000
  | 12 => 2483 / 1000000
  | 13 => 2047 / 1000000
  | 14 => 107 / 62500
  | 15 => 1449 / 1000000
  | 16 => 31 / 25000
  | _ => 0

theorem backlund_right_cell20_scalar :
    Real.log (backlundDirichletEnvelope 16 (1207 / 500 : ℝ)) ≤ 641 / 2000 := by
  have h := backlund_right_cell_log_certificate
    (a := 1207 / 500) (l := 641 / 2000) (v := 275543 / 200000)
    (qt := 9801 / 2500) (ut := 14027 / 1000000) rightCell20Q rightCell20U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell20Q, rightCell20U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell20U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell20 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 20 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      641 / 2000 := by
  have ha := backlund_right_cell_sigma (j := 20) (a := 1207 / 500) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (1207 / 500 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell20_scalar

#print axioms backlund_right_cell20_scalar
#print axioms backlund_right_cell20

end LiuWang.Proof.Campaign20260915.RosserCount
