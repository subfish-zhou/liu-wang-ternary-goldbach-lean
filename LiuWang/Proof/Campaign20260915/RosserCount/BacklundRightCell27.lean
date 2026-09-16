import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell27Q : ℕ → ℚ
  | 2 => 3969 / 2500
  | 3 => 25163 / 10000
  | 4 => 31753 / 10000
  | 5 => 2304 / 625
  | 6 => 513 / 125
  | 7 => 44571 / 10000
  | 8 => 47629 / 10000
  | 9 => 50327 / 10000
  | 10 => 2637 / 500
  | 11 => 54923 / 10000
  | 12 => 14229 / 2500
  | 13 => 47 / 8
  | 14 => 60447 / 10000
  | 15 => 62027 / 10000
  | 16 => 31753 / 5000
  | _ => 0

private def rightCell27U : ℕ → ℚ
  | 1 => 1
  | 2 => 3194 / 15625
  | 3 => 40379 / 500000
  | 4 => 20891 / 500000
  | 5 => 25063 / 1000000
  | 6 => 16507 / 1000000
  | 7 => 2899 / 250000
  | 8 => 8541 / 1000000
  | 9 => 3261 / 500000
  | 10 => 1281 / 250000
  | 11 => 4119 / 1000000
  | 12 => 27 / 8000
  | 13 => 2809 / 1000000
  | 14 => 2371 / 1000000
  | 15 => 253 / 125000
  | 16 => 873 / 500000
  | _ => 0

theorem backlund_right_cell27_scalar :
    Real.log (backlundDirichletEnvelope 16 (4581 / 2000 : ℝ)) ≤ 909 / 2500 := by
  have h := backlund_right_cell_log_certificate
    (a := 4581 / 2000) (l := 909 / 2500) (v := 1438397 / 1000000)
    (qt := 1789 / 500) (ut := 5411 / 250000) rightCell27Q rightCell27U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell27Q, rightCell27U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell27U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell27 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 27 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      909 / 2500 := by
  have ha := backlund_right_cell_sigma (j := 27) (a := 4581 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (4581 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell27_scalar

#print axioms backlund_right_cell27_scalar
#print axioms backlund_right_cell27

end LiuWang.Proof.Campaign20260915.RosserCount
