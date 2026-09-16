import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.RealLogIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding

def unitShiftRealBudget : ℝ :=
  realLogTail 3 / 2 - realLogTail (3 / 2) +
    (∫ x in (3 : ℝ)..5, realLogZeta x) / 2 -
    ∫ x in (3 / 2 : ℝ)..(5 / 2), realLogZeta x

def unitShiftFiniteBudget (B : ℝ) : ℝ :=
  (∫ x in (3 : ℝ)..B, realLogZeta x) / 2 -
    (∫ x in (3 / 2 : ℝ)..B, realLogZeta x) +
    (∫ x in (3 : ℝ)..5, realLogZeta x) / 2 -
    ∫ x in (3 / 2 : ℝ)..(5 / 2), realLogZeta x

theorem realLogTail_le_envelope {a : ℝ} (ha : 2 ≤ a) :
    realLogTail a ≤ 3 * 2 ^ (2 - a) / Real.log 2 := by
  have hi := log_zeta_right_integrable 0 ha
  have he := integral_re hi
  simp only [log_re, RCLike.re_to_complex] at he
  have h := (re_le_norm (∫ x in Set.Ioi a, log (riemannZeta (horizontalAt 0 x)))).trans
    (norm_integral_log_zeta_right_le 0 ha)
  rw [← he] at h
  simpa [realLogTail, realLogZeta, horizontalAt] using h

theorem realLogTail_sixteen_budget :
    0 ≤ realLogTail 16 ∧ realLogTail 16 ≤ 1 / 3000 := by
  refine ⟨realLogTail_nonneg (by norm_num), (realLogTail_le_envelope (by norm_num)).trans ?_⟩
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ (2 - (16 : ℝ)) = 1 / 16384 := by norm_num
  rw [hpow, div_le_iff₀ hp]
  linarith [Real.log_two_gt_d9]

theorem unitShiftRealBudget_eq_finite {B : ℝ} (hB : 1 < B) :
    unitShiftRealBudget = unitShiftFiniteBudget B - realLogTail B / 2 := by
  unfold unitShiftRealBudget unitShiftFiniteBudget
  rw [realLogTail_split (by norm_num : (1 : ℝ) < 3) hB,
    realLogTail_split (by norm_num : (1 : ℝ) < 3 / 2) hB]
  ring

theorem unitShiftRealBudget_finite_sixteen :
    unitShiftFiniteBudget 16 - 1 / 6000 ≤ unitShiftRealBudget ∧
      unitShiftRealBudget ≤ unitShiftFiniteBudget 16 := by
  rw [unitShiftRealBudget_eq_finite (by norm_num : (1 : ℝ) < 16)]
  constructor <;> linarith [realLogTail_sixteen_budget.1, realLogTail_sixteen_budget.2]

theorem horizontalLogMass_unitShift_lower {T : ℝ} (hT : T ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖) + unitShiftRealBudget ≤
      horizontalLogMass T := by
  have ht := real_log_tail_ratio_le_horizontal T (by norm_num : (1 : ℝ) < 3 / 2)
  have hi := real_log_interval_ratio_le_horizontal T
    (by norm_num : (1 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 5 / 2)
  norm_num only [show (2 : ℝ) * (3 / 2) = 3 by norm_num,
    show (2 : ℝ) * (5 / 2) = 5 by norm_num] at ht hi
  rw [lehman_shift_one_identity hT]
  unfold unitShiftRealBudget
  linarith

theorem horizontalLogMass_unitShift_finite_lower {T : ℝ} (hT : T ≠ 0) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
      Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖) +
      unitShiftFiniteBudget 16 - 1 / 6000 ≤ horizontalLogMass T := by
  linarith [horizontalLogMass_unitShift_lower hT, unitShiftRealBudget_finite_sixteen.1]

theorem horizontalLogMass_real_tail_upper {T c : ℝ} (hT : T ≠ 0) (hc : 1 < c) :
    horizontalLogMass T ≤
      (∫ x in (1 / 2 : ℝ)..c, Real.log ‖riemannZeta (horizontalAt T x)‖) +
        realLogTail c := by
  rw [horizontalLogMass_split hT c]
  linarith [horizontal_log_tail_le_real T hc]

theorem horizontalLogMass_finite_tail_upper {T c : ℝ} (hT : T ≠ 0) (hc : 1 < c) :
    horizontalLogMass T ≤
      (∫ x in (1 / 2 : ℝ)..c, Real.log ‖riemannZeta (horizontalAt T x)‖) +
        (∫ x in c..16, realLogZeta x) + 1 / 3000 := by
  have h := horizontalLogMass_real_tail_upper hT hc
  rw [realLogTail_split hc (by norm_num : (1 : ℝ) < 16)] at h
  linarith [realLogTail_sixteen_budget.2]

#print axioms realLogTail_sixteen_budget
#print axioms unitShiftRealBudget_finite_sixteen
#print axioms horizontalLogMass_unitShift_finite_lower
#print axioms horizontalLogMass_finite_tail_upper

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
