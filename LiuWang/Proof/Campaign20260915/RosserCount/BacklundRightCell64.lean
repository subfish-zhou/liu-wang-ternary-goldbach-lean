import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell64Q : ℕ → ℚ
  | 2 => 1083 / 1250
  | 3 => 3433 / 2500
  | 4 => 1083 / 625
  | 5 => 20117 / 10000
  | 6 => 5599 / 2500
  | 7 => 24323 / 10000
  | 8 => 25993 / 10000
  | 9 => 5493 / 2000
  | 10 => 14391 / 5000
  | 11 => 29973 / 10000
  | 12 => 31061 / 10000
  | 13 => 32061 / 10000
  | 14 => 8247 / 2500
  | 15 => 677 / 200
  | 16 => 34657 / 10000
  | _ => 0

private def rightCell64U : ℕ → ℚ
  | 1 => 1
  | 2 => 420463 / 1000000
  | 3 => 15831 / 62500
  | 4 => 176789 / 1000000
  | 5 => 66881 / 500000
  | 6 => 53251 / 500000
  | 7 => 17567 / 200000
  | 8 => 37163 / 500000
  | 9 => 64153 / 1000000
  | 10 => 14059 / 250000
  | 11 => 24961 / 500000
  | 12 => 5597 / 125000
  | 13 => 8103 / 200000
  | 14 => 577 / 15625
  | 15 => 16939 / 500000
  | 16 => 7813 / 250000
  | _ => 0

theorem backlund_right_cell64_scalar :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 : ℝ)) ≤ 3821 / 2500 := by
  have h := backlund_right_cell_log_certificate
    (a := 5 / 4) (l := 3821 / 2500) (v := 576341 / 125000)
    (qt := 6931 / 10000) (ut := 400019 / 200000) rightCell64Q rightCell64U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell64Q, rightCell64U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell64U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell64 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 64 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3821 / 2500 := by
  have ha := backlund_right_cell_sigma (j := 64) (a := 5 / 4) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (5 / 4 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell64_scalar

#print axioms backlund_right_cell64_scalar
#print axioms backlund_right_cell64

end LiuWang.Proof.Campaign20260915.RosserCount
