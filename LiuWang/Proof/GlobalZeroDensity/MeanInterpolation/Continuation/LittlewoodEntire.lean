import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.RectangleLog

/-! Littlewood's boundary identity for the actual entire detector and its produced arguments. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem rectangle_logs_integrable {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b c d : ℝ}
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) + c * I) ((b : ℂ) + d * I), f s ≠ 0) :
    IntervalIntegrable (horizontalLog f b d c) volume a b ∧
    IntervalIntegrable (horizontalLog f b d d) volume a b ∧
    IntervalIntegrable (rightLog f b d) volume c d ∧
    IntervalIntegrable (leftLog f a b d) volume c d := by
  obtain ⟨hc, hd, ha, hb⟩ := rectangle_nonzero_lines hn
  have hc' : ∀ x ∈ [[a, b]], lineValue f (c * I) 1 x ≠ 0 := by
    simpa [lineValue, add_comm] using hc
  have hd' : ∀ x ∈ [[a, b]], lineValue f (d * I) 1 x ≠ 0 := by
    simpa [lineValue, add_comm] using hd
  exact ⟨lineLog_integrable hf hc', lineLog_integrable hf hd',
    lineLog_integrable hf hb, lineLog_integrable hf ha⟩

theorem normalized_rectangle_re (f : ℂ → ℂ) (z w : ℂ) :
    2 * Real.pi * (RectangleIntegral' f z w).re = (RectangleIntegral f z w).im := by
  have he : (1 / (2 * (Real.pi : ℂ) * I)) = -I / (2 * Real.pi) := by
    field_simp
    simp [I_sq]
  rw [RectangleIntegral', he]
  simp [smul_eq_mul, Complex.mul_re, Complex.div_re, Complex.div_im]
  field_simp

theorem rectangle_littlewood_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b c d : ℝ}
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) + c * I) ((b : ℂ) + d * I), f s ≠ 0) :
    2 * Real.pi *
      (RectangleIntegral' (fun s => (s - ((a : ℂ) + c * I)) * logDeriv f s)
        ((a : ℂ) + c * I) ((b : ℂ) + d * I)).re =
      (∫ t in c..d, Real.log ‖f ((a : ℂ) + t * I)‖) -
        (∫ t in c..d, Real.log ‖f ((b : ℂ) + t * I)‖) +
          (∫ x in a..b, (horizontalLog f b d d x).im) -
            (∫ x in a..b, (horizontalLog f b d c x).im) := by
  rw [normalized_rectangle_re, rectangle_complex_log_formula hf hn]
  obtain ⟨hic, hid, hir, hil⟩ := rectangle_logs_integrable hf hn
  obtain ⟨_, _, _, hb⟩ := rectangle_nonzero_lines hn
  have hl : ∀ t ∈ [[c, d]], (leftLog f a b d t).re = Real.log ‖f ((a : ℂ) + t * I)‖ := by
    intro t ht
    rw [← leftLog_exp hf hn ht, Complex.norm_exp, Real.log_exp]
  have hr : ∀ t ∈ [[c, d]], (rightLog f b d t).re = Real.log ‖f ((b : ℂ) + t * I)‖ := by
    intro t ht
    rw [← rightLog_exp hf hb ht, Complex.norm_exp, Real.log_exp]
  have hlint := intervalIntegral.integral_congr (μ := volume) hl
  have hrint := intervalIntegral.integral_congr (μ := volume) hr
  change (∫ t in c..d, Complex.reCLM (leftLog f a b d t)) = _ at hlint
  change (∫ t in c..d, Complex.reCLM (rightLog f b d t)) = _ at hrint
  rw [Complex.reCLM.intervalIntegral_comp_comm hil] at hlint
  rw [Complex.reCLM.intervalIntegral_comp_comm hir] at hrint
  have hitop := Complex.imCLM.intervalIntegral_comp_comm hid
  have hibot := Complex.imCLM.intervalIntegral_comp_comm hic
  change (∫ x in a..b, (horizontalLog f b d d x).im) = _ at hitop
  change (∫ x in a..b, (horizontalLog f b d c x).im) = _ at hibot
  rw [hitop, hibot]
  simp only [add_im, sub_im, neg_im, I_mul_im]
  rw [← hlint, ← hrint]
  change -(∫ x in a..b, horizontalLog f b d c x).im +
    (∫ x in a..b, horizontalLog f b d d x).im -
    (∫ t in c..d, rightLog f b d t).re + (∫ t in c..d, leftLog f a b d t).re =
    (∫ t in c..d, leftLog f a b d t).re - (∫ t in c..d, rightLog f b d t).re +
    (∫ x in a..b, horizontalLog f b d d x).im - (∫ x in a..b, horizontalLog f b d c x).im
  ring

theorem actual_entireH_littlewood {y a U : ℝ} (hy : 3 < y) (ha : a ≤ 2) (hU : 0 ≤ U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) :
    2 * Real.pi *
      (∑ s ∈ (divisor_support_rectangle_finite (entireH y)
        ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).toFinset,
          (s.re - a) * (analyticOrderNatAt (entireH y) s : ℝ)) =
      (∫ t in -U..U, Real.log ‖entireH y ((a : ℂ) + t * I)‖) -
        (∫ t in -U..U, Real.log ‖entireH y ((2 : ℂ) + t * I)‖) +
          (∫ x in a..2, (horizontalLog (entireH y) 2 U U x).im) -
            (∫ x in a..2, (horizontalLog (entireH y) 2 U (-U) x).im) := by
  have hre : (((a : ℂ) - U * I)).re ≤ (((2 : ℂ) + U * I)).re := by simpa using ha
  have him : (((a : ℂ) - U * I)).im ≤ (((2 : ℂ) + U * I)).im := by
    simpa using (show -U ≤ U by linarith)
  have h := rectangle_littlewood_entire (differentiable_entireH y)
    (a := a) (b := 2) (c := -U) (d := U) (by simpa [sub_eq_add_neg] using hn)
  have hc := weightedDetector_rectangle_re hy hre him hn
  simp only [sub_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, sub_zero] at hc
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg, ofReal_ofNat] at h
  change 2 * Real.pi *
    (RectangleIntegral' (weightedDetectorKernel y ((a : ℂ) - U * I))
      ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re = _ at h
  rw [hc] at h
  exact h

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
