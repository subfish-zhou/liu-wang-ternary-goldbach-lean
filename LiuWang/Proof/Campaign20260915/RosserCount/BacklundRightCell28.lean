import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell28Q : ℕ → ℚ
  | 2 => 3147 / 2000
  | 3 => 1247 / 500
  | 4 => 31471 / 10000
  | 5 => 36537 / 10000
  | 6 => 10169 / 2500
  | 7 => 2761 / 625
  | 8 => 47207 / 10000
  | 9 => 49881 / 10000
  | 10 => 52273 / 10000
  | 11 => 13609 / 2500
  | 12 => 14103 / 2500
  | 13 => 58229 / 10000
  | 14 => 59911 / 10000
  | 15 => 30739 / 5000
  | 16 => 62943 / 10000
  | _ => 0

private def rightCell28U : ℕ → ℚ
  | 1 => 1
  | 2 => 207319 / 1000000
  | 3 => 82579 / 1000000
  | 4 => 42977 / 1000000
  | 5 => 3237 / 125000
  | 6 => 17119 / 1000000
  | 7 => 377 / 31250
  | 8 => 8909 / 1000000
  | 9 => 6819 / 1000000
  | 10 => 671 / 125000
  | 11 => 1081 / 250000
  | 12 => 3549 / 1000000
  | 13 => 37 / 12500
  | 14 => 2501 / 1000000
  | 15 => 2139 / 1000000
  | 16 => 1847 / 1000000
  | _ => 0

theorem backlund_right_cell28_scalar :
    Real.log (backlundDirichletEnvelope 16 (11351 / 5000 : ℝ)) ≤ 1857 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 11351 / 5000) (l := 1857 / 5000) (v := 724817 / 500000)
    (qt := 35217 / 10000) (ut := 727 / 31250) rightCell28Q rightCell28U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell28Q, rightCell28U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell28U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell28 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 28 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      1857 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 28) (a := 11351 / 5000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (11351 / 5000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell28_scalar

#print axioms backlund_right_cell28_scalar
#print axioms backlund_right_cell28

end LiuWang.Proof.Campaign20260915.RosserCount
