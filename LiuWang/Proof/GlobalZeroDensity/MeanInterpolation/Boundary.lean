import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Correlation

/-! The finite correlation has uniform strip bounds and correctly translated L2 boundary bounds. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Strip
open Complex.HadamardThreeLines

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem correlation_bounded {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (T : ℝ) :
    BddAbove ((norm ∘ correlation y σ T) '' verticalClosedStrip (1 / 2) (1 + delta y)) := by
  obtain ⟨B, hB⟩ := regularG_bounded hy
  have hg {w : ℂ} (hw : w ∈ verticalClosedStrip (1 / 2) (1 + delta y)) :
      ‖regularG y w‖ ≤ max B 0 := (hB (mem_image_of_mem _ hw)).trans (le_max_left _ _)
  refine ⟨(max B 0) ^ 2 * volume.real (Icc (-T) T), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro t _
  rw [norm_mul, norm_star]
  have h1 := hg (w := z + t * I) (by simpa [verticalClosedStrip] using hz)
  have h2 := hg (w := (σ : ℂ) + t * I) (by simpa [verticalClosedStrip] using hσ)
  nlinarith [norm_nonneg (regularG y (z + t * I)),
    norm_nonneg (regularG y ((σ : ℂ) + t * I))]

theorem correlation_diffContOnCl {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (T : ℝ) :
    DiffContOnCl ℂ (correlation y σ T) (verticalStrip (1 / 2) (1 + delta y)) := by
  have hd := delta_bounds hy
  apply DifferentiableOn.diffContOnCl
  rw [verticalStrip, Complex.closure_preimage_re, closure_Ioo (by linarith)]
  intro z hz
  exact (correlation_differentiable (by linarith : 0 < y)
    (closed_strip_safe hy (by simpa [verticalClosedStrip] using hσ)) T
    (closed_strip_safe hy hz)).differentiableWithinAt

theorem translated_squareWindow_le {y : ℝ} (hy : 10000 ≤ y) {z : ℂ}
    (hz : z.re ∈ Icc (1 / 2) (1 + delta y)) (T : ℝ) :
    (∫ t in Icc (-T) T, ‖regularG y (z + t * I)‖ ^ 2) ≤ weightedMean y z.re := by
  have heq (t : ℝ) : z + t * I = (z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [add_comm]
  simp_rw [heq]
  have hi := (regularG_strip_integrable hy hz).comp_add_right z.im
  have h := setIntegral_le_integral (s := Icc (-T) T) hi
    (Eventually.of_forall (fun t : ℝ =>
      sq_nonneg ‖regularG y ((z.re : ℂ) + ((t + z.im : ℝ) : ℂ) * I)‖))
  rw [integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => ‖regularG y ((z.re : ℂ) + t * I)‖ ^ 2)] at h
  exact h

theorem correlation_cauchy_schwarz {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (T : ℝ) {z : ℂ}
    (hz : z.re ∈ Icc (1 / 2) (1 + delta y)) :
    ‖correlation y σ T z‖ ≤
      Real.sqrt (weightedMean y z.re) * Real.sqrt (squareWindow y σ T) := by
  have hz' := closed_strip_safe hy (show z ∈ verticalClosedStrip (1 / 2) (1 + delta y) from hz)
  have hσ' := closed_strip_safe hy
    (show (σ : ℂ) ∈ verticalClosedStrip (1 / 2) (1 + delta y) by simpa [verticalClosedStrip] using hσ)
  have hc1 := vertical_continuous (by linarith : 0 < y) hz'
  have hc2 := vertical_continuous (by linarith : 0 < y) hσ'
  have hi1 := (hc1.norm.pow 2).integrableOn_Icc (a := -T) (b := T) (μ := volume)
  have hi2 := (hc2.norm.pow 2).integrableOn_Icc (a := -T) (b := T) (μ := volume)
  have hp1 := (memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable).mpr hi1
  have hp2 := (memLp_two_iff_integrable_sq_norm hc2.aestronglyMeasurable).mpr hi2
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hp1) (by simpa using hp2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hholder
  have hnorm := norm_integral_le_integral_norm
    (fun t : ℝ => regularG y (z + t * I) * star (regularG y ((σ : ℂ) + t * I)))
    (μ := volume.restrict (Icc (-T) T))
  simp only [norm_mul, norm_star] at hnorm
  have hroot := Real.sqrt_le_sqrt (translated_squareWindow_le hy hz T)
  exact hnorm.trans (hholder.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)))

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
