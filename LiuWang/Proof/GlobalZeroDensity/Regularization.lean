import LiuWang.Proof.GlobalZeroDensity.RightLine
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
The strip function must use the removable extension at s=1, not the totalized
quotient there. The origin and all cosine zeros are excluded by an actual open
strip. The detector preserves the analytic multiplicity of every zeta zero.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace LiuWang.Proof.GlobalZeroDensity

def g (y : ℝ) (s : ℂ) : ℂ :=
  (s - 1) / (s * Complex.cos (s / (2 * (y : ℂ)))) * f y s

def regularNumerator (y : ℝ) (s : ℂ) : ℂ :=
  Complex.zetaTimesSMinusOne_entire s * Q y s - (s - 1)

def regularG (y : ℝ) (s : ℂ) : ℂ :=
  regularNumerator y s / (s * Complex.cos (s / (2 * (y : ℂ))))

def regularStrip (y : ℝ) : Set ℂ := {s | 0 < s.re ∧ s.re < Real.pi * y}

theorem regularNumerator_eq {s : ℂ} (hs : s ≠ 1) (y : ℝ) :
    regularNumerator y s = (s - 1) * f y s := by
  rw [regularNumerator, Complex.zetaTimesSMinusOne_entire_eq_mul_riemannZeta hs, f]
  ring

theorem regularG_eq_g {s : ℂ} (hs : s ≠ 1) (y : ℝ) :
    regularG y s = g y s := by
  rw [regularG, regularNumerator_eq hs, g]
  ring

theorem regularG_one (y : ℝ) :
    regularG y 1 = Q y 1 / Complex.cos (1 / (2 * (y : ℂ))) := by
  simp [regularG, regularNumerator, Complex.zetaTimesSMinusOne_entire_one]

theorem g_one (y : ℝ) : g y 1 = 0 := by simp [g]

theorem g_zero (y : ℝ) : g y 0 = 0 := by simp [g]

theorem zero_not_mem_regularStrip (y : ℝ) : (0 : ℂ) ∉ regularStrip y := by
  simp [regularStrip]

theorem cos_ne_zero_of_abs_re_lt {z : ℂ} (hz : |z.re| < Real.pi / 2) :
    Complex.cos z ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hr : z.re = (2 * (k : ℝ) + 1) * Real.pi / 2 := by
    rw [hk]
    simp
  have hzero : Real.cos z.re = 0 := Real.cos_eq_zero_iff.mpr ⟨k, hr⟩
  exact (Real.cos_pos_of_mem_Ioo (abs_lt.mp hz)).ne' hzero

theorem strip_denominator_ne_zero {y : ℝ} (hy : 0 < y) {s : ℂ}
    (hs : s ∈ regularStrip y) :
    s * Complex.cos (s / (2 * (y : ℂ))) ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have := hs.1
    simp [h] at this
  refine mul_ne_zero hs0 (cos_ne_zero_of_abs_re_lt ?_)
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re,
    abs_of_pos (div_pos hs.1 (by positivity))]
  apply (div_lt_iff₀ (by positivity : 0 < 2 * y)).mpr
  nlinarith [hs.2]

theorem differentiable_regularNumerator (y : ℝ) :
    Differentiable ℂ (regularNumerator y) :=
  (Complex.zetaTimesSMinusOne_entire_differentiable.mul (differentiable_Q y)).sub
    (differentiable_id.sub_const 1)

theorem differentiableAt_regularG {y : ℝ} (hy : 0 < y) {s : ℂ}
    (hs : s ∈ regularStrip y) : DifferentiableAt ℂ (regularG y) s := by
  apply (differentiable_regularNumerator y s).div _ (strip_denominator_ne_zero hy hs)
  exact differentiableAt_id.mul ((differentiableAt_id.div_const _).ccos)

theorem analyticOn_regularG {y : ℝ} (hy : 0 < y) :
    AnalyticOnNhd ℂ (regularG y) (regularStrip y) := by
  have hopen : IsOpen (regularStrip y) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hd : DifferentiableOn ℂ (regularG y) (regularStrip y) :=
    fun _ hs => (differentiableAt_regularG hy hs).differentiableWithinAt
  exact hd.analyticOnNhd hopen

theorem continuous_vertical_regularG {y σ : ℝ} (hy : 0 < y)
    (hσ0 : 0 < σ) (hσy : σ < Real.pi * y) :
    Continuous (fun t : ℝ => regularG y ((σ : ℂ) + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : (σ : ℂ) + t * Complex.I ∈ regularStrip y := by
    simpa [regularStrip] using And.intro hσ0 hσy
  have hv : Continuous (fun t : ℝ => (σ : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * Complex.I)
    (g := regularG y) (differentiableAt_regularG hy hs).continuousAt hv.continuousAt

theorem intervalIntegrable_regularG_sq {y σ : ℝ} (hy : 0 < y)
    (hσ0 : 0 < σ) (hσy : σ < Real.pi * y) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2)
      volume (-u) u :=
  ((continuous_vertical_regularG hy hσ0 hσy).norm.pow 2).intervalIntegrable _ _

theorem analytic_zeta (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  analyticOn_riemannZeta s hs

theorem analyticOrder_H_ge_zeta (y : ℝ) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≤ analyticOrderAt (H y) s := by
  have hz := analytic_zeta s hs
  have hQ := (differentiable_Q y).analyticAt s
  have hfactor : H y = riemannZeta *
      (fun z => Q y z * (2 - riemannZeta z * Q y z)) :=
    funext (H_factorization y)
  have hother : AnalyticAt ℂ (fun z => Q y z * (2 - riemannZeta z * Q y z)) s :=
    hQ.mul (analyticAt_const.sub (hz.mul hQ))
  rw [hfactor, analyticOrderAt_mul hz hother]
  exact le_self_add

theorem log_norm_H_le_F (y : ℝ) (s : ℂ) :
    Real.log ‖H y s‖ ≤ F y s := by
  by_cases hzero : H y s = 0
  · simp only [hzero, norm_zero, Real.log_zero, F]
    exact sq_nonneg _
  have hnorm : ‖H y s‖ ≤ 1 + F y s := by
    exact (norm_sub_le 1 (f y s ^ 2)).trans_eq (by simp [F, norm_pow])
  exact (Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hzero)).trans (by linarith)

theorem intervalIntegrable_log_H_two {y : ℝ} (hy : 3 < y) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖H y ((2 : ℂ) + t * Complex.I)‖)
      volume (-u) u := by
  have hc : Continuous (fun t : ℝ => H y ((2 : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs : (2 : ℂ) + t * Complex.I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hv : Continuous (fun t : ℝ => (2 : ℂ) + t * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * Complex.I)
      (g := H y) (differentiableAt_H y hs).continuousAt hv.continuousAt
  exact (hc.norm.log (fun t =>
    norm_ne_zero_iff.mpr (H_ne_zero_on_two (by simp) hy))).intervalIntegrable _ _

end LiuWang.Proof.GlobalZeroDensity
