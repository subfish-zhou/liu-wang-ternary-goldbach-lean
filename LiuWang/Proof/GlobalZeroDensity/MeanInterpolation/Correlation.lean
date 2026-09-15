import LiuWang.Proof.GlobalZeroDensity.Strip.Consumer
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual finite correlation of the regularized detector, holomorphic in its first input. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Metric
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Strip
open Complex.HadamardThreeLines

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

def correlation (y σ T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc (-T) T, regularG y (z + t * I) *
    star (regularG y ((σ : ℂ) + t * I))

def squareWindow (y σ T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, ‖regularG y ((σ : ℂ) + t * I)‖ ^ 2

theorem regularStrip_add_im {y : ℝ} {z : ℂ} (hz : z ∈ regularStrip y) (t : ℝ) :
    z + t * I ∈ regularStrip y := by simpa [regularStrip] using hz

theorem vertical_continuous {y : ℝ} (hy : 0 < y) {z : ℂ}
    (hz : z ∈ regularStrip y) :
    Continuous (fun t : ℝ => regularG y (z + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ContinuousAt.comp (f := fun t : ℝ => z + t * I) (g := regularG y)
    (differentiableAt_regularG hy (regularStrip_add_im hz t)).continuousAt
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)

theorem correlation_integrable {y σ : ℝ} (hy : 0 < y)
    (hσ : (σ : ℂ) ∈ regularStrip y) (T : ℝ) {z : ℂ} (hz : z ∈ regularStrip y) :
    IntegrableOn (fun t : ℝ => regularG y (z + t * I) *
      star (regularG y ((σ : ℂ) + t * I))) (Icc (-T) T) :=
  ((vertical_continuous hy hz).mul (vertical_continuous hy hσ).star).integrableOn_Icc

theorem correlation_derivative_bound {y σ : ℝ} (hy : 0 < y)
    (hσ : (σ : ℂ) ∈ regularStrip y) (T : ℝ) {z : ℂ} (hz : z ∈ regularStrip y) :
    ∃ ε B : ℝ, 0 < ε ∧ closedBall z ε ⊆ regularStrip y ∧
      ∀ t ∈ Icc (-T) T, ∀ w ∈ closedBall z ε,
        ‖deriv (regularG y) (w + t * I) *
          star (regularG y ((σ : ℂ) + t * I))‖ ≤ B := by
  have hopen : IsOpen (regularStrip y) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hz)
  let J : Set (ℂ × ℝ) := closedBall z ε ×ˢ Icc (-T) T
  have hJ : IsCompact J := (isCompact_closedBall z ε).prod isCompact_Icc
  have hshift : Continuous (fun p : ℂ × ℝ => p.1 + p.2 * I) :=
    continuous_fst.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hmap : MapsTo (fun p : ℂ × ℝ => p.1 + p.2 * I) J (regularStrip y) :=
    fun p hp => regularStrip_add_im (hball hp.1) p.2
  have hder : ContinuousOn (fun p : ℂ × ℝ => deriv (regularG y) (p.1 + p.2 * I)) J :=
    (analyticOn_regularG hy).deriv.continuousOn.comp hshift.continuousOn hmap
  have hother : Continuous (fun p : ℂ × ℝ => star (regularG y ((σ : ℂ) + p.2 * I))) :=
    (vertical_continuous hy hσ).star.comp continuous_snd
  have hdc := hder.mul hother.continuousOn
  obtain ⟨B, hB⟩ := hJ.bddAbove_image hdc.norm
  refine ⟨ε, B, hε, hball, ?_⟩
  intro t ht w hw
  apply hB
  exact ⟨(w, t), ⟨hw, ht⟩, rfl⟩

theorem correlation_differentiable {y σ : ℝ} (hy : 0 < y)
    (hσ : (σ : ℂ) ∈ regularStrip y) (T : ℝ) {z : ℂ} (hz : z ∈ regularStrip y) :
    DifferentiableAt ℂ (correlation y σ T) z := by
  have hopen : IsOpen (regularStrip y) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  obtain ⟨ε, B, hε, hball, hB⟩ := correlation_derivative_bound hy hσ T hz
  let D : ℂ → ℝ → ℂ := fun w t =>
    deriv (regularG y) (w + t * I) * star (regularG y ((σ : ℂ) + t * I))
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => regularG y (w + t * I) *
        star (regularG y ((σ : ℂ) + t * I))) (volume.restrict (Icc (-T) T)) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact (correlation_integrable hy hσ T hw).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (D z) (volume.restrict (Icc (-T) T)) := by
    have hc : Continuous (D z) := by
      apply Continuous.mul
      · apply continuous_iff_continuousAt.mpr
        intro t
        exact ContinuousAt.comp (f := fun t : ℝ => z + t * I) (g := deriv (regularG y))
          ((analyticOn_regularG hy).deriv _ (regularStrip_add_im hz t)).continuousAt
          ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
      · exact (vertical_continuous hy hσ).star
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (-T) T), ∀ w ∈ closedBall z ε,
      ‖D w t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht w hw
    exact hB t ht w hw
  have hdiff : ∀ᵐ (t : ℝ) ∂volume.restrict (Icc (-T) T), ∀ w ∈ closedBall z ε,
      HasDerivAt (fun w : ℂ => regularG y (w + t * I) *
        star (regularG y ((σ : ℂ) + t * I))) (D w t) w := by
    filter_upwards with t w hw
    simpa [D] using
      (((differentiableAt_regularG hy (regularStrip_add_im (hball hw) t)).hasDerivAt.comp w
        ((hasDerivAt_id w).add_const (t * I))).mul_const
        (star (regularG y ((σ : ℂ) + t * I))))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds z hε) hmeas (correlation_integrable hy hσ T hz) hdmeas hbound
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top)) hdiff).2.differentiableAt

theorem squareWindow_nonneg (y σ T : ℝ) : 0 ≤ squareWindow y σ T :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem correlation_self (y σ T : ℝ) :
    correlation y σ T σ = (squareWindow y σ T : ℂ) := by
  have heq (w : ℂ) : w * star w = (‖w‖ ^ 2 : ℝ) := by
    rw [Complex.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq w
  simp_rw [correlation, heq]
  exact integral_ofReal

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
