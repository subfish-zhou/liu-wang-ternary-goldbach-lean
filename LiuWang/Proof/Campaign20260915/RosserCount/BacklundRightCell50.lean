import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell50Q : ℕ → ℚ
  | 2 => 2349 / 2000
  | 3 => 3723 / 2000
  | 4 => 2349 / 1000
  | 5 => 27271 / 10000
  | 6 => 30361 / 10000
  | 7 => 32973 / 10000
  | 8 => 8809 / 2500
  | 9 => 37231 / 10000
  | 10 => 39017 / 10000
  | 11 => 5079 / 1250
  | 12 => 21053 / 5000
  | 13 => 43463 / 10000
  | 14 => 22359 / 5000
  | 15 => 45887 / 10000
  | 16 => 46981 / 10000
  | _ => 0

private def rightCell50U : ℕ → ℚ
  | 1 => 1
  | 2 => 154487 / 500000
  | 3 => 1943 / 12500
  | 4 => 19093 / 200000
  | 5 => 65409 / 1000000
  | 6 => 24011 / 500000
  | 7 => 36983 / 1000000
  | 8 => 14747 / 500000
  | 9 => 24159 / 1000000
  | 10 => 1263 / 62500
  | 11 => 8597 / 500000
  | 12 => 7419 / 500000
  | 13 => 2591 / 200000
  | 14 => 11427 / 1000000
  | 15 => 10167 / 1000000
  | 16 => 9113 / 1000000
  | _ => 0

theorem backlund_right_cell50_scalar :
    Real.log (backlundDirichletEnvelope 16 (3389 / 2000 : ℝ)) ≤ 291 / 400 := by
  have h := backlund_right_cell_log_certificate
    (a := 3389 / 2000) (l := 291 / 400) (v := 517447 / 250000)
    (qt := 3851 / 2000) (ut := 10497 / 50000) rightCell50Q rightCell50U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell50Q, rightCell50U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell50U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell50 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 50 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      291 / 400 := by
  have ha := backlund_right_cell_sigma (j := 50) (a := 3389 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (3389 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell50_scalar

#print axioms backlund_right_cell50_scalar
#print axioms backlund_right_cell50

end LiuWang.Proof.Campaign20260915.RosserCount
