import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Constants
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityLogs

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524

def originalBracket (L x : ℝ) : ℝ :=
  (1.8771 * L ^ (1 - 9 * x / 20) * sourceNu (L ^ x) * (x * Real.log L) ^ (1 / 15 : ℝ) *
      (254231 / Real.log (10000 * L ^ x * Real.log (L ^ x)) + 17102) *
        Real.log (10000 * L ^ x * Real.log (L ^ x)) ^ 6 +
    1.0159 * 16541 * L ^ (1 - x / 2) * sourceNu (L ^ x) *
      Real.log (10000 * x * Real.log L) ^ 6) *
    Real.exp (-0.478 * L / Real.log (10000 * Real.pi * L ^ x))

def logNu (s : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log s + 2.50637 / Real.log s

def heightLog (s : ℝ) : ℝ := Real.log (10000 * s)

def densityLog (s : ℝ) : ℝ := s + heightLog s

def logBracket (L s : ℝ) : ℝ :=
  L * (1.8771 * Real.exp (-(9 / 20 : ℝ) * s) * logNu s * s ^ (1 / 15 : ℝ) *
      (254231 / densityLog s + 17102) * densityLog s ^ 6 +
    1.0159 * 16541 * Real.exp (-(1 / 2 : ℝ) * s) * logNu s * heightLog s ^ 6) *
      Real.exp (-0.478 * L / (s + Real.log lowHeight))

theorem originalBracket_eq_logBracket {L x : ℝ} (hL : 0 < L) (hx : 0 < x)
    (hl : 0 < Real.log L) :
    originalBracket L x = logBracket L (x * Real.log L) := by
  have hr : 0 < L ^ x := Real.rpow_pos_of_pos hL x
  have he (c : ℝ) : L ^ (1 - c * x) = L * Real.exp (-c * (x * Real.log L)) := by
    rw [Real.rpow_def_of_pos hL, show Real.log L * (1 - c * x) =
      Real.log L + (-c * (x * Real.log L)) by ring,
      Real.exp_add, Real.exp_log hL]
  have hp : Real.log (10000 * Real.pi * L ^ x) =
      x * Real.log L + Real.log lowHeight := by
    rw [Real.log_mul (by positivity : (10000 * Real.pi : ℝ) ≠ 0) hr.ne',
      Real.log_rpow hL]
    unfold lowHeight
    ring
  have hz : Real.log (10000 * L ^ x * Real.log (L ^ x)) =
      densityLog (x * Real.log L) := by
    rw [Real.log_rpow hL, show 10000 * L ^ x * (x * Real.log L) =
      L ^ x * (10000 * (x * Real.log L)) by ring,
      Real.log_mul hr.ne' (by positivity), Real.log_rpow hL]
    rfl
  have hn : sourceNu (L ^ x) = logNu (x * Real.log L) := by
    simp only [sourceNu, logNu, Real.log_rpow hL]
  unfold originalBracket logBracket
  rw [show 1 - 9 * x / 20 = 1 - (9 / 20 : ℝ) * x by ring,
    show 1 - x / 2 = 1 - (1 / 2 : ℝ) * x by ring, he, he, hn, hp, hz]
  unfold heightLog
  rw [show 10000 * x * Real.log L = 10000 * (x * Real.log L) by ring]
  ring

theorem modulus_parameter {L : ℝ} {q : ℕ}
    (hL : 3100 ≤ L) (hq : L ^ (3 : ℕ) ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ L ^ (6 : ℕ)) :
    3 ≤ Real.log q / Real.log L ∧ Real.log q / Real.log L ≤ 6 ∧
      L ^ (Real.log q / Real.log L) = (q : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hl : 0 < Real.log L := Real.log_pos (by linarith)
  have hq0 := (pow_pos hL0 3).trans_le hq
  have hlo := Real.log_le_log (pow_pos hL0 3) hq
  have hhi := Real.log_le_log hq0 hq1
  rw [Real.log_pow] at hlo hhi
  norm_num only [Nat.cast_ofNat] at hlo hhi
  refine ⟨(le_div_iff₀ hl).mpr hlo, (div_le_iff₀ hl).mpr hhi, ?_⟩
  rw [Real.rpow_def_of_pos hL0, mul_div_cancel₀ _ hl.ne', Real.exp_log hq0]

theorem modulus_logBracket {L : ℝ} {q : ℕ}
    (hL : 3100 ≤ L) (hq : L ^ (3 : ℕ) ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ L ^ (6 : ℕ)) :
    originalBracket L (Real.log q / Real.log L) = logBracket L (Real.log q) := by
  have hx := modulus_parameter hL hq hq1
  have hl : 0 < Real.log L := Real.log_pos (by linarith)
  rw [originalBracket_eq_logBracket (by linarith) (by linarith [hx.1]) hl,
    div_mul_cancel₀ _ hl.ne']

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524
