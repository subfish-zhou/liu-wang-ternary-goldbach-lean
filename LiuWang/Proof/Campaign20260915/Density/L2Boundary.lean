import LiuWang.Proof.Campaign20260915.Density.L2Correlation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology
open Complex.HadamardThreeLines

namespace LiuWang.Proof.Campaign20260915.Density.L2Strip

theorem correlation_bounded {f : ℂ → ℂ} {a b sigma : ℝ}
    (hb : BddAbove ((norm ∘ f) '' verticalClosedStrip a b))
    (hs : sigma ∈ Icc a b) (T : ℝ) :
    BddAbove ((norm ∘ correlation f sigma T) '' verticalClosedStrip a b) := by
  obtain ⟨B, hB⟩ := hb
  have hg {w : ℂ} (hw : w ∈ verticalClosedStrip a b) :
      ‖f w‖ ≤ max B 0 := (hB (mem_image_of_mem _ hw)).trans (le_max_left _ _)
  refine ⟨(max B 0) ^ 2 * volume.real (Icc (-T) T), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro t _
  rw [norm_mul, norm_star]
  have h1 := hg (w := z + t * I) (by simpa [verticalClosedStrip] using hz)
  have h2 := hg (w := (sigma : ℂ) + t * I) (by simpa [verticalClosedStrip] using hs)
  nlinarith [norm_nonneg (f (z + t * I)), norm_nonneg (f ((sigma : ℂ) + t * I))]

theorem correlation_diffContOnCl {f : ℂ → ℂ} {lo hi a b sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi)) (hab : a < b)
    (hinside : verticalClosedStrip a b ⊆ verticalStrip lo hi) (hs : sigma ∈ Icc a b) (T : ℝ) :
    DiffContOnCl ℂ (correlation f sigma T) (verticalStrip a b) := by
  apply DifferentiableOn.diffContOnCl
  rw [verticalStrip, Complex.closure_preimage_re, closure_Ioo hab.ne]
  intro z hz
  exact (correlation_differentiable hf
    (hinside (by simpa only [verticalClosedStrip, mem_preimage, ofReal_re] using hs)) T
    (hinside hz)).differentiableWithinAt

theorem translated_squareWindow_le {f : ℂ → ℂ} {z : ℂ}
    (hi : Integrable (fun t : ℝ => ‖f ((z.re : ℂ) + t * I)‖ ^ 2)) (T : ℝ) :
    (∫ t in Icc (-T) T, ‖f (z + t * I)‖ ^ 2) ≤ squareMean f z.re := by
  have he (t : ℝ) : z + t * I = (z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [add_comm]
  simp_rw [he]
  have h := setIntegral_le_integral (s := Icc (-T) T) (hi.comp_add_right z.im)
    (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖f ((z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * I)‖))
  rw [integral_add_right_eq_self (μ := volume) (fun t : ℝ => ‖f ((z.re : ℂ) + t * I)‖ ^ 2)] at h
  exact h

theorem correlation_cauchy_schwarz {f : ℂ → ℂ} {lo hi sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi))
    (hs : (sigma : ℂ) ∈ verticalStrip lo hi) (T : ℝ) {z : ℂ}
    (hz : z ∈ verticalStrip lo hi)
    (hi : Integrable (fun t : ℝ => ‖f ((z.re : ℂ) + t * I)‖ ^ 2)) :
    ‖correlation f sigma T z‖ ≤ Real.sqrt (squareMean f z.re) * Real.sqrt (squareWindow f sigma T) := by
  have hc1 := vertical_continuous hf hz
  have hc2 := vertical_continuous hf hs
  have hi1 := (hc1.norm.pow 2).integrableOn_Icc (a := -T) (b := T) (μ := volume)
  have hi2 := (hc2.norm.pow 2).integrableOn_Icc (a := -T) (b := T) (μ := volume)
  have hp1 := (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr hi1
  have hp2 := (memLp_two_iff_integrable_sq_norm hc2.aestronglyMeasurable).mpr hi2
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hp1) (by simpa using hp2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  have hn := norm_integral_le_integral_norm
    (fun t : ℝ => f (z + t * I) * star (f ((sigma : ℂ) + t * I)))
    (μ := volume.restrict (Icc (-T) T))
  simp only [norm_mul, norm_star] at hn
  exact hn.trans (hh.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (translated_squareWindow_le hi T)) (Real.sqrt_nonneg _)))

theorem correlation_sq_bound {f : ℂ → ℂ} {lo hi sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi))
    (hs : (sigma : ℂ) ∈ verticalStrip lo hi) (T : ℝ) {z : ℂ}
    (hz : z ∈ verticalStrip lo hi)
    (hi : Integrable (fun t : ℝ => ‖f ((z.re : ℂ) + t * I)‖ ^ 2)) :
    ‖correlation f sigma T z ^ 2‖ ≤ squareMean f z.re * squareWindow f sigma T := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (correlation_cauchy_schwarz hf hs T hz hi) 2
  rw [mul_pow, Real.sq_sqrt (squareMean_nonneg _ _),
    Real.sq_sqrt (squareWindow_nonneg _ _ _), ← norm_pow] at h
  exact h

end LiuWang.Proof.Campaign20260915.Density.L2Strip
