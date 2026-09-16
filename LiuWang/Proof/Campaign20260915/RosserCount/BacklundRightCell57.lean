import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCellKernel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private def rightCell57Q : ℕ → ℚ
  | 2 => 10227 / 10000
  | 3 => 1621 / 1000
  | 4 => 10227 / 5000
  | 5 => 23747 / 10000
  | 6 => 26437 / 10000
  | 7 => 28711 / 10000
  | 8 => 15341 / 5000
  | 9 => 1621 / 500
  | 10 => 16987 / 5000
  | 11 => 1769 / 500
  | 12 => 4583 / 1250
  | 13 => 7569 / 2000
  | 14 => 38939 / 10000
  | 15 => 39957 / 10000
  | 16 => 40909 / 10000
  | _ => 0

private def rightCell57U : ℕ → ℚ
  | 1 => 1
  | 2 => 359623 / 1000000
  | 3 => 197701 / 1000000
  | 4 => 129329 / 1000000
  | 5 => 93043 / 1000000
  | 6 => 35549 / 500000
  | 7 => 56637 / 1000000
  | 8 => 9301 / 200000
  | 9 => 19543 / 500000
  | 10 => 33461 / 1000000
  | 11 => 1817 / 62500
  | 12 => 25569 / 1000000
  | 13 => 22721 / 1000000
  | 14 => 10183 / 500000
  | 15 => 3679 / 200000
  | 16 => 669 / 40000
  | _ => 0

theorem backlund_right_cell57_scalar :
    Real.log (backlundDirichletEnvelope 16 (2951 / 2000 : ℝ)) ≤ 5007 / 5000 := by
  have h := backlund_right_cell_log_certificate
    (a := 2951 / 2000) (l := 5007 / 5000) (v := 1361043 / 500000)
    (qt := 13183 / 10000) (ut := 112551 / 200000) rightCell57Q rightCell57U
    (by norm_num) (by rfl)
    (by
      intro n hn hn'
      interval_cases n <;>
        norm_num [rightCell57Q, rightCell57U, logNaturalCenter, logNaturalRaw, roundRational,
          Nat.log2_eq_log_two, backlundExpLower, Finset.sum_range_succ])
    (by norm_num) (by norm_num)
    (by norm_num [logNaturalCenter, logNaturalRaw, roundRational,
      Nat.log2_eq_log_two, Finset.sum_range_succ])
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
    (by norm_num [rightCell57U, Finset.sum_range_succ]) (by norm_num)
    (by norm_num [backlundExpLower, Finset.sum_range_succ])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

theorem backlund_right_cell57 {θ : ℝ} (hθ : 0 ≤ θ)
    (hθj : θ ≤ 57 * Real.pi / 128) :
    Real.log (backlundDirichletEnvelope 16 (5 / 4 + (33 / 25 : ℝ) * Real.cos θ)) ≤
      5007 / 5000 := by
  have ha := backlund_right_cell_sigma (j := 57) (a := 2951 / 2000) (by norm_num)
    (by norm_num [backlundRightPhase, backlundRightAngle, unitRepeatedSquare,
      roundQComplex, squareQComplex, unitTaylor, roundRational, realIPower, imagIPower,
      Finset.sum_range_succ]) hθ (by simpa using hθj)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  have hx : (1 : ℝ) < 5 / 4 + (33 / 25) * Real.cos θ := by linarith
  have hm := backlundDirichletEnvelope_antitone (N := 16) (by norm_num)
    (by norm_num : (2951 / 2000 : ℝ) ∈ Set.Ioi 1) hx ha
  exact (Real.log_le_log (backlundDirichletEnvelope_pos (by norm_num) hx) hm).trans
    backlund_right_cell57_scalar

#print axioms backlund_right_cell57_scalar
#print axioms backlund_right_cell57

end LiuWang.Proof.Campaign20260915.RosserCount
