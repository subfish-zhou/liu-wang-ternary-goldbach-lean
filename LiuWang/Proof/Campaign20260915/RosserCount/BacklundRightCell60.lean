import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell60Q : ℕ → ℚ
  | 2 => 9559 / 10000
  | 3 => 947 / 625
  | 4 => 19119 / 10000
  | 5 => 22197 / 10000
  | 6 => 24711 / 10000
  | 7 => 26837 / 10000
  | 8 => 28679 / 10000
  | 9 => 1894 / 625
  | 10 => 31757 / 10000
  | 11 => 33071 / 10000
  | 12 => 34271 / 10000
  | 13 => 283 / 80
  | 14 => 36397 / 10000
  | 15 => 37349 / 10000
  | 16 => 38239 / 10000
  | _ => 0

private def rightCell60U : ℕ → ℚ
  | 1 => 1
  | 2 => 192233 / 500000
  | 3 => 43953 / 200000
  | 4 => 739 / 5000
  | 5 => 54321 / 500000
  | 6 => 21123 / 250000
  | 7 => 6831 / 100000
  | 8 => 56819 / 1000000
  | 9 => 48297 / 1000000
  | 10 => 8353 / 200000
  | 11 => 36623 / 1000000
  | 12 => 32481 / 1000000
  | 13 => 14543 / 500000
  | 14 => 26261 / 1000000
  | 15 => 5969 / 250000
  | 16 => 21843 / 1000000
  | _ => 0

theorem backlund_right_cell60_scalar :
    Real.log (backlundDirichletEnvelope 16 (862 / 625 : ℝ)) ≤ 5897 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 862 / 625) (l := 5897 / 5000) (v := 3252159 / 1000000)
    (qt := 10513 / 10000) (ut := 921633 / 1000000) rightCell60Q rightCell60U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell60Q, rightCell60U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell60U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell60 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 60 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      5897 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 60) (a := 862 / 625) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (862 / 625 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell60_scalar

#print axioms backlund_right_cell60_scalar
#print axioms backlund_right_cell60

end LiuWang.Proof.Campaign20260915.RosserCount
