import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Correlation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter Metric
open scoped Topology
open Complex.HadamardThreeLines

namespace LiuWang.Proof.Campaign20260915.Density.L2Strip

def correlation (f : ℂ → ℂ) (sigma T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc (-T) T, f (z + t * I) * star (f ((sigma : ℂ) + t * I))

def squareWindow (f : ℂ → ℂ) (sigma T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, ‖f ((sigma : ℂ) + t * I)‖ ^ 2

def squareMean (f : ℂ → ℂ) (sigma : ℝ) : ℝ :=
  ∫ t : ℝ, ‖f ((sigma : ℂ) + t * I)‖ ^ 2

theorem strip_add_im {lo hi : ℝ} {z : ℂ} (hz : z ∈ verticalStrip lo hi) (t : ℝ) :
    z + t * I ∈ verticalStrip lo hi := by simpa [verticalStrip] using hz

theorem vertical_continuous {f : ℂ → ℂ} {lo hi : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi)) {z : ℂ} (hz : z ∈ verticalStrip lo hi) :
    Continuous (fun t : ℝ => f (z + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ContinuousAt.comp (f := fun t : ℝ => z + t * I) (g := f)
    (hf _ (strip_add_im hz t)).continuousAt
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)

theorem correlation_integrable {f : ℂ → ℂ} {lo hi sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi))
    (hs : (sigma : ℂ) ∈ verticalStrip lo hi) (T : ℝ) {z : ℂ} (hz : z ∈ verticalStrip lo hi) :
    IntegrableOn (fun t : ℝ => f (z + t * I) * star (f ((sigma : ℂ) + t * I))) (Icc (-T) T) :=
  ((vertical_continuous hf hz).mul (vertical_continuous hf hs).star).integrableOn_Icc

theorem correlation_derivative_bound {f : ℂ → ℂ} {lo hi sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi))
    (hs : (sigma : ℂ) ∈ verticalStrip lo hi) (T : ℝ) {z : ℂ} (hz : z ∈ verticalStrip lo hi) :
    ∃ e B : ℝ, 0 < e ∧ closedBall z e ⊆ verticalStrip lo hi ∧
      ∀ t ∈ Icc (-T) T, ∀ w ∈ closedBall z e,
        ‖deriv f (w + t * I) * star (f ((sigma : ℂ) + t * I))‖ ≤ B := by
  have hopen : IsOpen (verticalStrip lo hi) := isOpen_Ioo.preimage Complex.continuous_re
  obtain ⟨e, he, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hz)
  let J : Set (ℂ × ℝ) := closedBall z e ×ˢ Icc (-T) T
  have hJ : IsCompact J := (isCompact_closedBall z e).prod isCompact_Icc
  have hshift : Continuous (fun p : ℂ × ℝ => p.1 + p.2 * I) := by fun_prop
  have hmap : MapsTo (fun p : ℂ × ℝ => p.1 + p.2 * I) J (verticalStrip lo hi) :=
    fun p hp => strip_add_im (hball hp.1) p.2
  have hder : ContinuousOn (fun p : ℂ × ℝ => deriv f (p.1 + p.2 * I)) J :=
    hf.deriv.continuousOn.comp hshift.continuousOn hmap
  have hother : Continuous (fun p : ℂ × ℝ => star (f ((sigma : ℂ) + p.2 * I))) :=
    (vertical_continuous hf hs).star.comp continuous_snd
  obtain ⟨B, hB⟩ := hJ.bddAbove_image (hder.mul hother.continuousOn).norm
  refine ⟨e, B, he, hball, ?_⟩
  intro t ht w hw
  exact hB ⟨(w, t), ⟨hw, ht⟩, rfl⟩

theorem correlation_differentiable {f : ℂ → ℂ} {lo hi sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi))
    (hs : (sigma : ℂ) ∈ verticalStrip lo hi) (T : ℝ) {z : ℂ} (hz : z ∈ verticalStrip lo hi) :
    DifferentiableAt ℂ (correlation f sigma T) z := by
  have hopen : IsOpen (verticalStrip lo hi) := isOpen_Ioo.preimage Complex.continuous_re
  obtain ⟨e, B, he, hball, hB⟩ := correlation_derivative_bound hf hs T hz
  let D : ℂ → ℝ → ℂ := fun w t => deriv f (w + t * I) * star (f ((sigma : ℂ) + t * I))
  have hm : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => f (w + t * I) * star (f ((sigma : ℂ) + t * I)))
        (volume.restrict (Icc (-T) T)) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (correlation_integrable hf hs T hw).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (D z) (volume.restrict (Icc (-T) T)) :=
    ((vertical_continuous hf.deriv hz).mul (vertical_continuous hf hs).star).aestronglyMeasurable
  have hb : ∀ᵐ t ∂volume.restrict (Icc (-T) T), ∀ w ∈ closedBall z e, ‖D w t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht w hw
    exact hB t ht w hw
  have hd : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc (-T) T), ∀ w ∈ closedBall z e,
      HasDerivAt (fun w : ℂ => f (w + t * I) * star (f ((sigma : ℂ) + t * I))) (D w t) w := by
    filter_upwards with t w hw
    simpa [D] using
      (((hf _ (strip_add_im (hball hw) t)).differentiableAt.hasDerivAt.comp w
        ((hasDerivAt_id w).add_const (t * I))).mul_const (star (f ((sigma : ℂ) + t * I))))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds z he) hm (correlation_integrable hf hs T hz) hdm hb
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top)) hd).2.differentiableAt

theorem squareWindow_nonneg (f : ℂ → ℂ) (sigma T : ℝ) : 0 ≤ squareWindow f sigma T :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem squareMean_nonneg (f : ℂ → ℂ) (sigma : ℝ) : 0 ≤ squareMean f sigma :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem correlation_self (f : ℂ → ℂ) (sigma T : ℝ) :
    correlation f sigma T sigma = (squareWindow f sigma T : ℂ) := by
  have he (w : ℂ) : w * star w = (‖w‖ ^ 2 : ℝ) := by
    rw [Complex.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq w
  simp_rw [correlation, he]
  exact integral_ofReal

end LiuWang.Proof.Campaign20260915.Density.L2Strip
