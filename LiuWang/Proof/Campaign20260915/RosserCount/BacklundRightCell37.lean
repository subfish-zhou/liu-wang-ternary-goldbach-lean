import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell37Q : ℕ → ℚ
  | 2 => 14291 / 10000
  | 3 => 5663 / 2500
  | 4 => 28583 / 10000
  | 5 => 2074 / 625
  | 6 => 2309 / 625
  | 7 => 20061 / 5000
  | 8 => 343 / 80
  | 9 => 5663 / 1250
  | 10 => 11869 / 2500
  | 11 => 24721 / 5000
  | 12 => 12809 / 2500
  | 13 => 26443 / 5000
  | 14 => 27207 / 5000
  | 15 => 55837 / 10000
  | 16 => 57167 / 10000
  | _ => 0

private def rightCell37U : ℕ → ℚ
  | 1 => 1
  | 2 => 9581 / 40000
  | 3 => 10381 / 100000
  | 4 => 57367 / 1000000
  | 5 => 36211 / 1000000
  | 6 => 24863 / 1000000
  | 7 => 9047 / 500000
  | 8 => 687 / 50000
  | 9 => 10777 / 1000000
  | 10 => 8673 / 1000000
  | 11 => 57 / 8000
  | 12 => 1191 / 200000
  | 13 => 5049 / 1000000
  | 14 => 2167 / 500000
  | 15 => 3759 / 1000000
  | 16 => 3291 / 1000000
  | _ => 0

theorem backlund_right_cell37_scalar :
    Real.log (backlundDirichletEnvelope 16 (20619 / 10000 : ℝ)) ≤ 4651 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 20619 / 10000) (l := 4651 / 10000) (v := 1592149 / 1000000)
    (qt := 14721 / 5000) (ut := 6197 / 125000) rightCell37Q rightCell37U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell37Q, rightCell37U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell37U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell37 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 37 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      4651 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 37) (a := 20619 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (20619 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell37_scalar

#print axioms backlund_right_cell37_scalar
#print axioms backlund_right_cell37

end LiuWang.Proof.Campaign20260915.RosserCount
