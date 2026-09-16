import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell25Q : ℕ → ℚ
  | 2 => 16143 / 10000
  | 3 => 12793 / 5000
  | 4 => 16143 / 5000
  | 5 => 37483 / 10000
  | 6 => 4173 / 1000
  | 7 => 1133 / 250
  | 8 => 4843 / 1000
  | 9 => 51173 / 10000
  | 10 => 53627 / 10000
  | 11 => 27923 / 5000
  | 12 => 57873 / 10000
  | 13 => 59737 / 10000
  | 14 => 61463 / 10000
  | 15 => 6307 / 1000
  | 16 => 64573 / 10000
  | _ => 0

private def rightCell25U : ℕ → ℚ
  | 1 => 1
  | 2 => 19903 / 100000
  | 3 => 38707 / 500000
  | 4 => 39613 / 1000000
  | 5 => 11779 / 500000
  | 6 => 7703 / 500000
  | 7 => 269 / 25000
  | 8 => 1971 / 250000
  | 9 => 5993 / 1000000
  | 10 => 4689 / 1000000
  | 11 => 939 / 250000
  | 12 => 3067 / 1000000
  | 13 => 509 / 200000
  | 14 => 1071 / 500000
  | 15 => 57 / 31250
  | 16 => 157 / 100000
  | _ => 0

theorem backlund_right_cell25_scalar :
    Real.log (backlundDirichletEnvelope 16 (2329 / 1000 : ℝ)) ≤ 1747 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 2329 / 1000) (l := 1747 / 5000) (v := 1418141 / 1000000)
    (qt := 36847 / 10000) (ut := 1889 / 100000) rightCell25Q rightCell25U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell25Q, rightCell25U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell25U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell25 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 25 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      1747 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 25) (a := 2329 / 1000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2329 / 1000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell25_scalar

#print axioms backlund_right_cell25_scalar
#print axioms backlund_right_cell25

end LiuWang.Proof.Campaign20260915.RosserCount
