import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.LineLog

/-! Genuine line integration by parts for the produced logarithm. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem lineLog_anchor (f : ℂ → ℂ) (p v : ℂ) (b : ℝ) (l : ℂ) :
    lineLog f p v b l b = l := by simp [lineLog]

theorem lineLog_integrable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {a b : ℝ} {l : ℂ}
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0) :
    IntervalIntegrable (lineLog f p v b l) volume a b :=
  (lineLog_continuousOn hf hn).intervalIntegrable

theorem lineSlope_integrable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {a b : ℝ}
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0) :
    IntervalIntegrable (lineSlope f p v) volume a b :=
  (show ContinuousOn (lineSlope f p v) [[a, b]] from
    fun t ht => (lineSlope_continuousAt hf (hn t ht)).continuousWithinAt).intervalIntegrable

theorem line_integral_parts {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v c : ℂ} {a b : ℝ} {l : ℂ}
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0) :
    (∫ t in a..b, (p + t * v - c) * lineSlope f p v t) =
      (p + b * v - c) * l -
        (p + a * v - c) * lineLog f p v b l a -
          v * (∫ t in a..b, lineLog f p v b l t) := by
  have hd : ∀ t ∈ [[a, b]], HasDerivAt (fun t : ℝ => p + t * v - c) v t := by
    intro t _
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v).const_add p).sub_const c
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hd
    (fun _ ht => lineLog_hasDerivAt hf ht hn (l := l))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => v) volume a b)
    (lineSlope_integrable hf hn)
  simpa only [lineLog_anchor, intervalIntegral.integral_const_mul] using h

theorem weighted_line_integrable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v c : ℂ} {a b : ℝ}
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (p + t * v - c) * lineSlope f p v t) volume a b :=
  (lineSlope_integrable hf hn).continuousOn_mul (by fun_prop)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
