import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell55Q : ℕ → ℚ
  | 2 => 10667 / 10000
  | 3 => 16907 / 10000
  | 4 => 4267 / 2000
  | 5 => 24769 / 10000
  | 6 => 1103 / 400
  | 7 => 29947 / 10000
  | 8 => 16001 / 5000
  | 9 => 6763 / 2000
  | 10 => 8859 / 2500
  | 11 => 36903 / 10000
  | 12 => 19121 / 5000
  | 13 => 19737 / 5000
  | 14 => 8123 / 2000
  | 15 => 10419 / 2500
  | 16 => 4267 / 1000
  | _ => 0

private def rightCell55U : ℕ → ℚ
  | 1 => 1
  | 2 => 344143 / 1000000
  | 3 => 184391 / 1000000
  | 4 => 118423 / 1000000
  | 5 => 21001 / 250000
  | 6 => 63451 / 1000000
  | 7 => 12513 / 250000
  | 8 => 8151 / 200000
  | 9 => 33997 / 1000000
  | 10 => 2891 / 100000
  | 11 => 4993 / 200000
  | 12 => 5459 / 250000
  | 13 => 3861 / 200000
  | 14 => 2153 / 125000
  | 15 => 1549 / 100000
  | 16 => 1753 / 125000
  | _ => 0

theorem backlund_right_cell55_scalar :
    Real.log (backlundDirichletEnvelope 16 (1539 / 1000 : ℝ)) ≤ 567 / 625 := by
  have h := backlund_right_cell_log_certificate
    (a := 1539 / 1000) (l := 567 / 625) (v := 1238633 / 500000)
    (qt := 934 / 625) (ut := 52037 / 125000) rightCell55Q rightCell55U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell55Q, rightCell55U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell55U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell55 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 55 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      567 / 625 := by
  have ha := backlund_right_cell_sigma (j := 55) (a := 1539 / 1000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (1539 / 1000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell55_scalar

#print axioms backlund_right_cell55_scalar
#print axioms backlund_right_cell55

end LiuWang.Proof.Campaign20260915.RosserCount
