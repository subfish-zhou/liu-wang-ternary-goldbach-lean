import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.HLittlewood

/-! Joint continuity of the actual finite mean, paying simultaneous side/height perturbations. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Interval Topology

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem M_rescale (y σ U : ℝ) :
    M y σ U = U * ∫ t in (-1 : ℝ)..1, F y ((σ : ℂ) + (U * t : ℝ) * I) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => F y ((σ : ℂ) + t * I)) (a := -1) (b := 1) U
  simpa [M, smul_eq_mul] using h.symm

theorem continuous_M_exponential_param (y : ℝ) :
    Continuous (fun p : ℝ × ℝ => M y (1 - Real.exp p.1) p.2) := by
  let V : (ℝ × ℝ) → ℝ → ℝ := fun p t =>
    F y (((1 - Real.exp p.1 : ℝ) : ℂ) + (p.2 * t : ℝ) * I)
  have hV : Continuous V.uncurry := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hs : (((1 - Real.exp p.1.1 : ℝ) : ℂ) + (p.1.2 * p.2 : ℝ) * I) ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, one_re] at hh
      linarith [Real.exp_pos p.1.1]
    have hf := (differentiableAt_f y hs).continuousAt
    have hc : ContinuousAt
        (fun p : (ℝ × ℝ) × ℝ => (((1 - Real.exp p.1.1 : ℝ) : ℂ) + (p.1.2 * p.2 : ℝ) * I)) p := by
      fun_prop
    exact (hf.comp (f := fun p : (ℝ × ℝ) × ℝ =>
      (((1 - Real.exp p.1.1 : ℝ) : ℂ) + (p.1.2 * p.2 : ℝ) * I)) hc).norm.pow 2
  have hi : Continuous (fun p : ℝ × ℝ => ∫ t in Icc (-1 : ℝ) 1, V p t) :=
    continuous_parametric_integral_of_continuous hV isCompact_Icc
  have he : (fun p : ℝ × ℝ => M y (1 - Real.exp p.1) p.2) =
      (fun p : ℝ × ℝ => p.2 * ∫ t in Icc (-1 : ℝ) 1, V p t) := by
    funext p
    rw [M_rescale, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
  rw [he]
  exact continuous_snd.mul hi

theorem continuousAt_M_below_one (y : ℝ) {σ U : ℝ} (hσ : σ < 1) :
    ContinuousAt (fun p : ℝ × ℝ => M y p.1 p.2) (σ, U) := by
  have hparam : ContinuousAt (fun p : ℝ × ℝ => (Real.log (1 - p.1), p.2)) (σ, U) :=
    ((continuousAt_const.sub continuousAt_fst).log (by linarith : 1 - σ ≠ 0)).prodMk continuousAt_snd
  have hc := (continuous_M_exponential_param y).continuousAt.comp hparam
  have he : (fun p : ℝ × ℝ => M y (1 - Real.exp (Real.log (1 - p.1))) p.2) =ᶠ[𝓝 (σ, U)]
      (fun p : ℝ × ℝ => M y p.1 p.2) := by
    filter_upwards [continuousAt_fst.eventually (gt_mem_nhds hσ)] with p hp
    rw [Real.exp_log (by linarith : 0 < 1 - p.1)]
    congr 1
    ring
  exact hc.congr_of_eventuallyEq he.symm

theorem M_joint_limit (y : ℝ) {σ U : ℝ} (hσ : σ < 1) {a b : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 σ)) (hb : Tendsto b atTop (𝓝 U)) :
    Tendsto (fun n => M y (a n) (b n)) atTop (𝓝 (M y σ U)) := by
  have hp : Tendsto (fun n => (a n, b n)) atTop (𝓝 (σ, U)) := ha.prodMk_nhds hb
  have hc : Tendsto (fun p : ℝ × ℝ => M y p.1 p.2) (𝓝 (σ, U)) (𝓝 (M y σ U)) :=
    (continuousAt_M_below_one y (σ := σ) (U := U) hσ).tendsto
  exact Filter.Tendsto.comp (g := fun p : ℝ × ℝ => M y p.1 p.2)
    (f := fun n : ℕ => (a n, b n)) hc hp

theorem M_nearby_budget {y σ U η : ℝ} (hσ : σ < 1) (hη : 0 < η) :
    ∃ ε > 0, ∀ a b : ℝ, |a - σ| < ε → |b - U| < ε →
      M y a b < M y σ U + η := by
  have he := (continuousAt_M_below_one y (σ := σ) (U := U) hσ).eventually
    (gt_mem_nhds (lt_add_of_pos_right (M y σ U) hη))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb
  apply hball (y := (a, b))
  simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro ha hb

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
