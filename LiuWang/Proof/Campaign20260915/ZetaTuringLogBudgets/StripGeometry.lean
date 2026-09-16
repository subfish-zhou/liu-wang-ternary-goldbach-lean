import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.UnitShiftFiniteBudget
import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanGammaBudget
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaWinding

def stripGeometryError (T x : ℝ) : ℝ :=
  (1 + (5 / 4 - x) / 3) * (Real.log ‖horizontalAt T x‖ - Real.log T) -
    (Real.log ‖horizontalAt T x - 1‖ - Real.log T)

theorem horizontal_log_norm_continuous {T : ℝ} (hT : T ≠ 0) (a : ℂ) :
    a.im = 0 → Continuous (fun x => Real.log ‖horizontalAt T x - a‖) := by
  intro ha
  apply Continuous.log
  · apply Continuous.norm
    unfold horizontalAt
    fun_prop
  · intro x
    apply norm_ne_zero_iff.mpr
    intro he
    have hi := congrArg Complex.im he
    simp [horizontalAt, ha] at hi
    exact hT hi

theorem stripGeometryError_continuous {T : ℝ} (hT : T ≠ 0) :
    Continuous (stripGeometryError T) := by
  have h0 := horizontal_log_norm_continuous hT 0 (by simp)
  have h1 := horizontal_log_norm_continuous hT 1 (by simp)
  simp only [sub_zero] at h0
  exact ((by fun_prop : Continuous (fun x : ℝ => 1 + (5 / 4 - x) / 3)).mul
    (h0.sub continuous_const)).sub (h1.sub continuous_const)

theorem stripGeometryError_le {T x : ℝ} (hT : 0 < T) (hx : x ≤ 5 / 4) :
    stripGeometryError T x ≤ (1 + (5 / 4 - x) / 3) * x ^ 2 / (2 * T ^ 2) := by
  have h0 := log_norm_sub_log_im_bounds
    (z := horizontalAt T x) (by simpa [horizontalAt] using hT)
  have h1 := log_norm_sub_log_im_bounds
    (z := horizontalAt T x - 1) (by simpa [horizontalAt] using hT)
  simp [horizontalAt] at h0 h1
  have hw : 0 ≤ 1 + (5 / 4 - x) / 3 := by linarith
  have hm := mul_le_mul_of_nonneg_left h0.2 hw
  rw [mul_add, ← mul_div_assoc] at hm
  dsimp [stripGeometryError, horizontalAt]
  linarith [h1.1]

theorem integral_stripGeometry_polynomial (T : ℝ) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4),
      (1 + (5 / 4 - x) / 3) * x ^ 2 / (2 * T ^ 2)) = 681 / (2048 * T ^ 2) := by
  have he (x : ℝ) :
      (1 + (5 / 4 - x) / 3) * x ^ 2 / (2 * T ^ 2) =
        ((17 / 24 : ℝ) * x ^ 2 - x ^ 3 / 6) / T ^ 2 := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun x : ℝ => (17 / 24 : ℝ) * x ^ 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ => x ^ 3 / 6)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    integral_pow, integral_pow]
  norm_num
  ring

theorem integral_stripGeometryError_le {T : ℝ} (hT : 0 < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), stripGeometryError T x) ≤ 681 / (2048 * T ^ 2) := by
  rw [← integral_stripGeometry_polynomial T]
  exact intervalIntegral.integral_mono_on (by norm_num)
    ((stripGeometryError_continuous hT.ne').intervalIntegrable _ _)
    ((by fun_prop : Continuous
      (fun x : ℝ => (1 + (5 / 4 - x) / 3) * x ^ 2 / (2 * T ^ 2))).intervalIntegrable _ _)
    (fun _ hx => stripGeometryError_le hT hx.2)

theorem integral_stripGeometryError_original_budget {T : ℝ} (hT : 168 * Real.pi < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), stripGeometryError T x) < 1 / 500000 := by
  have ht : 504 < T := by linarith [Real.pi_gt_three]
  refine (integral_stripGeometryError_le (by linarith : 0 < T)).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg (T - 504)]

theorem source_C2_pointwise_counterexample :
    168 * Real.pi < (528 : ℝ) ∧
      (1 + 1 / 500000 : ℝ) * 528 < ‖horizontalAt 528 (5 / 4)‖ := by
  constructor
  · linarith [Real.pi_lt_d4]
  · have hs : ‖horizontalAt 528 (5 / 4)‖ ^ 2 = (528 : ℝ) ^ 2 + (5 / 4 : ℝ) ^ 2 := by
      rw [← normSq_eq_norm_sq]
      norm_num [normSq_apply, horizontalAt]
    nlinarith [norm_nonneg (horizontalAt 528 (5 / 4))]

#print axioms integral_stripGeometryError_original_budget
#print axioms source_C2_pointwise_counterexample

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
