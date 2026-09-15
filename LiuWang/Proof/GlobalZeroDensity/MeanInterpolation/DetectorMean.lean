import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.RemoveWeight

/-! The actual source Lemma 3.5, with the stronger constant 1861. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem M_unweight_split {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) :
    M y σ y ≤ M y σ 1 + (13 / 5) * weightedMean y σ := by
  have hd := delta_bounds hy
  have hσ1 : σ ≠ 1 := by linarith [hσ.2]
  have hstrip : σ ∈ Icc (1 / 2) (1 + delta y) := by
    constructor <;> linarith [hσ.1, hσ.2]
  let v (t : ℝ) := F y ((σ : ℂ) + t * I)
  let w (t : ℝ) := ‖regularG y ((σ : ℂ) + t * I)‖ ^ 2
  have hv : Continuous v := continuous_vertical_F y hσ1
  have hvy : Integrable ((Icc (-y) y).indicator v) :=
    hv.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hv1 : Integrable ((Icc (-1 : ℝ) 1).indicator v) :=
    hv.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hw : Integrable w := regularG_strip_integrable hy hstrip
  have hpoint (t : ℝ) :
      (Icc (-y) y).indicator v t ≤ (Icc (-1 : ℝ) 1).indicator v t + (13 / 5) * w t := by
    have hw0 : 0 ≤ w t := sq_nonneg _
    have hv0 : 0 ≤ v t := sq_nonneg _
    by_cases ht : t ∈ Icc (-y) y
    · rw [indicator_of_mem ht]
      by_cases ht1 : t ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem ht1]; linarith
      · rw [indicator_of_notMem ht1, zero_add]
        exact F_high_unweight hy hσ
          (le_of_lt (lt_of_not_ge (fun h => ht1 (abs_le.mp h)))) (abs_le.mpr ht)
    · rw [indicator_of_notMem ht]
      exact add_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) _) (by positivity)
  have h := integral_mono hvy (hv1.fun_add (hw.const_mul (13 / 5))) hpoint
  rw [integral_add hv1 (hw.const_mul (13 / 5)), integral_const_mul,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc] at h
  simp only [M, intervalIntegral.integral_of_le (show -y ≤ y by linarith),
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    ← integral_Icc_eq_integral_Ioc]
  exact h

theorem M_lemma_3_5_sharp {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) :
    M y σ y ≤ 1861 * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) := by
  have hd := delta_bounds hy
  have hstrip : σ ∈ Icc (1 / 2) (1 + delta y) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have h := M_unweight_split hy hσ
  have hlo := M_low_sharp hy hσ
  have hhi := weightedMean_source_shape hy hstrip
  linarith

theorem lemma_3_5 {y σ : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 - delta y)) :
    M y σ y ≤ (331839 / 100) * y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) := by
  have hy' : 10000 ≤ y := by linarith [log_six_ge_one]
  have h := M_lemma_3_5_sharp hy' hσ
  have hL := log_ge_nine hy'
  have hp : 0 ≤ y ^ (4 * (1 - σ)) * Real.log y ^ (6 * σ - 1) := by positivity
  nlinarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
