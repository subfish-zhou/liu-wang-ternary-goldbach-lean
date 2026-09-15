import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.DetectorMean
import LiuWang.Proof.GlobalZeroDensity.LogBoundary
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-! Actual logarithmic detector integrals, including legitimate integrability across zeros. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem log_H_vertical_integrable (y : ℝ) {σ : ℝ} (hσ : σ ≠ 1) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖H y ((σ : ℂ) + t * I)‖) volume (-T) T := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t _
  have hs : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hσ this
  have ha : AnalyticAt ℂ (H y) ((σ : ℂ) + t * I) :=
    analyticAt_const.sub ((((analytic_zeta _ hs).mul ((differentiable_Q y).analyticAt _)).sub
      analyticAt_const).pow 2)
  have hg : AnalyticAt ℝ (fun t : ℝ => (σ : ℂ) + t * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact MeromorphicAt.comp_analyticAt (g := fun t : ℝ => (σ : ℂ) + t * I)
    ha.meromorphicAt hg

theorem log_H_integral_le_M (y : ℝ) {σ : ℝ} (hσ : σ ≠ 1) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, Real.log ‖H y ((σ : ℂ) + t * I)‖) ≤ M y σ T :=
  intervalIntegral.integral_mono_on (by linarith)
    (log_H_vertical_integrable y hσ T) (intervalIntegrable_F y T hσ)
    (fun t _ => log_norm_H_le_F y _)

theorem littlewood_vertical_budget {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) :
    IntervalIntegrable (fun t : ℝ =>
      Real.log ‖H y ((σ : ℂ) + t * I)‖ - Real.log ‖H y ((2 : ℂ) + t * I)‖)
        volume (-y) y ∧
    (∫ t in -y..y,
      Real.log ‖H y ((σ : ℂ) + t * I)‖ - Real.log ‖H y ((2 : ℂ) + t * I)‖) ≤
      1861 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) +
        16 * y / (y - 1) ^ 2 := by
  have hd := delta_bounds hy
  have hσ1 : σ ≠ 1 := by linarith [hσ.2]
  have hl := log_H_vertical_integrable y hσ1 y
  have hr := intervalIntegrable_log_H_two (by linarith : 3 < y) y
  refine ⟨hl.sub hr, ?_⟩
  rw [intervalIntegral.integral_sub hl hr]
  have hu := log_H_integral_le_M y hσ1 (by linarith : 0 ≤ y)
  have hm := M_lemma_3_5_sharp hy hσ
  have ha := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -y ≤ y)
    hr.neg hr.abs (fun t _ => neg_le_abs _)
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at ha
  have hb := abs_log_integral_two_le (by linarith : 5 ≤ y) (by linarith : 0 ≤ y)
  linarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
