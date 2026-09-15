import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.HWeightedDetection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! A continuous logarithm produced by integrating the actual logarithmic derivative. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval Topology

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def lineValue (f : ℂ → ℂ) (p v : ℂ) (t : ℝ) : ℂ := f (p + t * v)

def lineSlope (f : ℂ → ℂ) (p v : ℂ) (t : ℝ) : ℂ := v * logDeriv f (p + t * v)

def lineLog (f : ℂ → ℂ) (p v : ℂ) (b : ℝ) (l : ℂ) (t : ℝ) : ℂ :=
  l + ∫ u in b..t, lineSlope f p v u

theorem lineValue_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) (p v : ℂ) (t : ℝ) :
    HasDerivAt (lineValue f p v) (v * deriv f (p + t * v)) t := by
  have hp : HasDerivAt (fun u : ℝ => p + u * v) v t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v).const_add p
  change HasDerivAt (fun u : ℝ => f (p + u * v)) _ t
  simpa only [Function.comp_def, mul_comm] using (hf (p + t * v)).hasDerivAt.comp t hp

theorem lineSlope_continuousAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {t : ℝ} (hn : lineValue f p v t ≠ 0) :
    ContinuousAt (lineSlope f p v) t := by
  have hq : ContinuousAt (logDeriv f) (p + t * v) :=
    ((hf.analyticAt _).deriv.continuousAt.div (hf.continuous.continuousAt) hn)
  exact continuousAt_const.mul (hq.comp (f := fun u : ℝ => p + u * v) (by fun_prop))

theorem lineSlope_measurable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (p v : ℂ) :
    StronglyMeasurable (lineSlope f p v) := by
  have hm : MeromorphicOn f univ := fun s _ => (hf.analyticAt s).meromorphicAt
  have hq : Measurable (logDeriv f) :=
    (show Meromorphic (logDeriv f) from fun s => hm.logDeriv s (mem_univ s)).measurable
  exact (measurable_const.mul (hq.comp (by fun_prop))).stronglyMeasurable

theorem lineLog_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {a b t : ℝ} {l : ℂ} (ht : t ∈ [[a, b]])
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0) :
    HasDerivAt (lineLog f p v b l) (lineSlope f p v t) t := by
  have hi : IntervalIntegrable (lineSlope f p v) volume b t :=
    (show ContinuousOn (lineSlope f p v) [[b, t]] from fun u hu =>
      (lineSlope_continuousAt hf (hn u (uIcc_subset_uIcc (right_mem_uIcc) ht hu))).continuousWithinAt).intervalIntegrable
  exact (intervalIntegral.integral_hasDerivAt_right hi
    (lineSlope_measurable hf p v).stronglyMeasurableAtFilter
    (lineSlope_continuousAt hf (hn t ht))).const_add l

theorem lineLog_continuousOn {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {a b : ℝ} {l : ℂ}
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0) :
    ContinuousOn (lineLog f p v b l) [[a, b]] :=
  fun _ ht => (lineLog_hasDerivAt hf ht hn).continuousAt.continuousWithinAt

theorem exp_lineLog {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {a b t : ℝ} {l : ℂ} (ht : t ∈ [[a, b]])
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0)
    (hl : Complex.exp l = lineValue f p v b) :
    Complex.exp (lineLog f p v b l t) = lineValue f p v t := by
  let K : ℝ → ℂ := fun u => lineValue f p v u * Complex.exp (-lineLog f p v b l u)
  have hd : ∀ u ∈ [[b, t]], HasDerivAt K 0 u := by
    intro u hu
    have hum := uIcc_subset_uIcc right_mem_uIcc ht hu
    have hL := lineLog_hasDerivAt hf hum hn (l := l)
    have hD := (lineValue_hasDerivAt hf p v u).mul hL.neg.cexp
    have hzero : v * deriv f (p + u * v) * Complex.exp (-lineLog f p v b l u) +
        lineValue f p v u * (Complex.exp (-lineLog f p v b l u) * -lineSlope f p v u) = 0 := by
      have hne : f (p + u * v) ≠ 0 := hn u hum
      change v * deriv f (p + u * v) * Complex.exp (-lineLog f p v b l u) +
        f (p + u * v) * (Complex.exp (-lineLog f p v b l u) *
          -(v * (deriv f (p + u * v) / f (p + u * v)))) = 0
      calc
        _ = v * deriv f (p + u * v) * Complex.exp (-lineLog f p v b l u) *
            (1 - f (p + u * v) * (f (p + u * v))⁻¹) := by ring
        _ = 0 := by rw [mul_inv_cancel₀ hne]; ring
    simp only [Pi.neg_apply] at hD
    rw [hzero] at hD
    exact hD
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume b t)
  have hk : K t = 1 := by
    have hb : K b = 1 := by
      simp only [K, lineLog, intervalIntegral.integral_same, add_zero, ← hl,
        Complex.exp_neg, mul_inv_cancel₀ (Complex.exp_ne_zero l)]
    simpa only [intervalIntegral.integral_zero, hb, sub_eq_zero] using he.symm
  dsimp [K] at hk
  rw [Complex.exp_neg] at hk
  have he := congrArg (fun z : ℂ => z * Complex.exp (lineLog f p v b l t)) hk
  simpa only [mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one, one_mul] using he.symm

theorem lineLog_re {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {p v : ℂ} {a b t : ℝ} {l : ℂ} (ht : t ∈ [[a, b]])
    (hn : ∀ u ∈ [[a, b]], lineValue f p v u ≠ 0)
    (hl : Complex.exp l = lineValue f p v b) :
    (lineLog f p v b l t).re = Real.log ‖lineValue f p v t‖ := by
  rw [← exp_lineLog hf ht hn hl, Complex.norm_exp, Real.log_exp]

theorem entireH_line_log {y : ℝ} {p v : ℂ} {a b : ℝ}
    (hn : ∀ t ∈ [[a, b]], entireH y (p + t * v) ≠ 0) :
    ContinuousOn (lineLog (entireH y) p v b (Complex.log (entireH y (p + b * v)))) [[a, b]] ∧
    ∀ t ∈ [[a, b]],
      Complex.exp (lineLog (entireH y) p v b (Complex.log (entireH y (p + b * v))) t) =
        entireH y (p + t * v) := by
  exact ⟨lineLog_continuousOn (differentiable_entireH y) hn, fun t ht =>
    exp_lineLog (differentiable_entireH y) ht hn (Complex.exp_log (hn b right_mem_uIcc))⟩

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
