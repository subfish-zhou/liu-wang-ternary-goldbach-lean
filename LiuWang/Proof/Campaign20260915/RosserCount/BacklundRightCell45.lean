import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell45Q : ℕ → ℚ
  | 2 => 1597 / 1250
  | 3 => 81 / 40
  | 4 => 25553 / 10000
  | 5 => 14833 / 5000
  | 6 => 33027 / 10000
  | 7 => 8967 / 2500
  | 8 => 3833 / 1000
  | 9 => 40501 / 10000
  | 10 => 42443 / 10000
  | 11 => 221 / 50
  | 12 => 11451 / 2500
  | 13 => 47279 / 10000
  | 14 => 9729 / 2000
  | 15 => 49917 / 10000
  | 16 => 51107 / 10000
  | _ => 0

private def rightCell45U : ℕ → ℚ
  | 1 => 1
  | 2 => 139353 / 500000
  | 3 => 65997 / 500000
  | 4 => 77669 / 1000000
  | 5 => 51479 / 1000000
  | 6 => 2299 / 62500
  | 7 => 27687 / 1000000
  | 8 => 4329 / 200000
  | 9 => 17421 / 1000000
  | 10 => 7173 / 500000
  | 11 => 2407 / 200000
  | 12 => 10251 / 1000000
  | 13 => 4423 / 500000
  | 14 => 1929 / 250000
  | 15 => 1359 / 200000
  | 16 => 377 / 62500
  | _ => 0

theorem backlund_right_cell45_scalar :
    Real.log (backlundDirichletEnvelope 16 (18433 / 10000 : ℝ)) ≤ 601 / 1000 := by
  have h := backlund_right_cell_log_certificate
    (a := 18433 / 10000) (l := 601 / 1000) (v := 1823851 / 1000000)
    (qt := 23381 / 10000) (ut := 22889 / 200000) rightCell45Q rightCell45U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell45Q, rightCell45U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell45U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell45 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 45 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      601 / 1000 := by
  have ha := backlund_right_cell_sigma (j := 45) (a := 18433 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (18433 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell45_scalar

#print axioms backlund_right_cell45_scalar
#print axioms backlund_right_cell45

end LiuWang.Proof.Campaign20260915.RosserCount
