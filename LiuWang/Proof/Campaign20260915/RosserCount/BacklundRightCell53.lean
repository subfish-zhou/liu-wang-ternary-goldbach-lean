import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell53Q : ℕ → ℚ
  | 2 => 11103 / 10000
  | 3 => 8799 / 5000
  | 4 => 22207 / 10000
  | 5 => 25781 / 10000
  | 6 => 14351 / 5000
  | 7 => 31171 / 10000
  | 8 => 3331 / 1000
  | 9 => 35197 / 10000
  | 10 => 7377 / 2000
  | 11 => 38411 / 10000
  | 12 => 7961 / 2000
  | 13 => 41087 / 10000
  | 14 => 1691 / 400
  | 15 => 2169 / 500
  | 16 => 22207 / 5000
  | _ => 0

private def rightCell53U : ℕ → ℚ
  | 1 => 1
  | 2 => 329461 / 1000000
  | 3 => 2151 / 12500
  | 4 => 54267 / 500000
  | 5 => 75919 / 1000000
  | 6 => 3543 / 62500
  | 7 => 22143 / 500000
  | 8 => 17879 / 500000
  | 9 => 29609 / 1000000
  | 10 => 2501 / 100000
  | 11 => 2147 / 100000
  | 12 => 18677 / 1000000
  | 13 => 1643 / 100000
  | 14 => 14589 / 1000000
  | 15 => 13063 / 1000000
  | 16 => 589 / 50000
  | _ => 0

theorem backlund_right_cell53_scalar :
    Real.log (backlundDirichletEnvelope 16 (16019 / 10000 : ℝ)) ≤ 8271 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 16019 / 10000) (l := 8271 / 10000) (v := 457297 / 200000)
    (qt := 1043 / 625) (ut := 313131 / 1000000) rightCell53Q rightCell53U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell53Q, rightCell53U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell53U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell53 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 53 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      8271 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 53) (a := 16019 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (16019 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell53_scalar

#print axioms backlund_right_cell53_scalar
#print axioms backlund_right_cell53

end LiuWang.Proof.Campaign20260915.RosserCount
