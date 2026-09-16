import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell59Q : ℕ → ℚ
  | 2 => 9783 / 10000
  | 3 => 3101 / 2000
  | 4 => 9783 / 5000
  | 5 => 4543 / 2000
  | 6 => 3161 / 1250
  | 7 => 3433 / 1250
  | 8 => 29349 / 10000
  | 9 => 31011 / 10000
  | 10 => 16249 / 5000
  | 11 => 33843 / 10000
  | 12 => 35071 / 10000
  | 13 => 36201 / 10000
  | 14 => 37247 / 10000
  | 15 => 38221 / 10000
  | 16 => 9783 / 2500
  | _ => 0

private def rightCell59U : ℕ → ℚ
  | 1 => 1
  | 2 => 7519 / 20000
  | 3 => 106071 / 500000
  | 4 => 141339 / 1000000
  | 5 => 51579 / 500000
  | 6 => 15951 / 200000
  | 7 => 64159 / 1000000
  | 8 => 53137 / 1000000
  | 9 => 9 / 200
  | 10 => 19391 / 500000
  | 11 => 16951 / 500000
  | 12 => 937 / 31250
  | 13 => 1339 / 50000
  | 14 => 24121 / 1000000
  | 15 => 10941 / 500000
  | 16 => 19977 / 1000000
  | _ => 0

theorem backlund_right_cell59_scalar :
    Real.log (backlundDirichletEnvelope 16 (7057 / 5000 : ℝ)) ≤ 5571 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 7057 / 5000) (l := 5571 / 5000) (v := 1523497 / 500000)
    (qt := 5703 / 5000) (ut := 388463 / 500000) rightCell59Q rightCell59U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell59Q, rightCell59U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell59U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell59 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 59 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      5571 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 59) (a := 7057 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (7057 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell59_scalar

#print axioms backlund_right_cell59_scalar
#print axioms backlund_right_cell59

end LiuWang.Proof.Campaign20260915.RosserCount
