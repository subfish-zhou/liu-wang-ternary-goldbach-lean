import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell30Q : ℕ → ℚ
  | 2 => 7721 / 5000
  | 3 => 979 / 400
  | 4 => 6177 / 2000
  | 5 => 2241 / 625
  | 6 => 19959 / 5000
  | 7 => 5419 / 1250
  | 8 => 46327 / 10000
  | 9 => 48951 / 10000
  | 10 => 51299 / 10000
  | 11 => 26711 / 5000
  | 12 => 55361 / 10000
  | 13 => 7143 / 1250
  | 14 => 11759 / 2000
  | 15 => 15083 / 2500
  | 16 => 6177 / 1000
  | _ => 0

private def rightCell30U : ℕ → ℚ
  | 1 => 1
  | 2 => 213483 / 1000000
  | 3 => 8651 / 100000
  | 4 => 45571 / 1000000
  | 5 => 27721 / 1000000
  | 6 => 18467 / 1000000
  | 7 => 131 / 10000
  | 8 => 9729 / 1000000
  | 9 => 1871 / 250000
  | 10 => 2959 / 500000
  | 11 => 2393 / 500000
  | 12 => 1971 / 500000
  | 13 => 3299 / 1000000
  | 14 => 2797 / 1000000
  | 15 => 1199 / 500000
  | 16 => 2077 / 1000000
  | _ => 0

theorem backlund_right_cell30_scalar :
    Real.log (backlundDirichletEnvelope 16 (22279 / 10000 : ℝ)) ≤ 3883 / 10000 := by
  have h := backlund_right_cell_log_certificate
    (a := 22279 / 10000) (l := 3883 / 10000) (v := 737171 / 500000)
    (qt := 8511 / 2500) (ut := 1353 / 50000) rightCell30Q rightCell30U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell30Q, rightCell30U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell30U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell30 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 30 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      3883 / 10000 := by
  have ha := backlund_right_cell_sigma (j := 30) (a := 22279 / 10000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (22279 / 10000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell30_scalar

#print axioms backlund_right_cell30_scalar
#print axioms backlund_right_cell30

end LiuWang.Proof.Campaign20260915.RosserCount
