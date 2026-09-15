import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.LittlewoodEntire

/-! Exact removal of the degree-two pole-cancelling factor, not an assumed correction cost. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval Topology

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def poleFactor (s : ℂ) : ℂ := s - 1

theorem poleFactor_differentiable : Differentiable ℂ poleFactor :=
  differentiable_id.sub_const 1

theorem poleFactor_boundary {a U : ℝ} (ha : a < 1) (hU : 0 < U) :
    ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), poleFactor s ≠ 0 := by
  intro s hs hz
  have hs1 : s = 1 := sub_eq_zero.mp hz
  subst s
  have ha0 : a ≠ 1 := ne_of_lt ha
  have hU0 : U ≠ 0 := ne_of_gt hU
  simp [RectangleBorder, mem_reProdIm, hU0, Ne.symm ha0, Ne.symm hU0] at hs

theorem poleFactor_weighted_contour {a U : ℝ} (ha : a < 1) (hU : 0 < U) :
    RectangleIntegral' (fun s => (s - ((a : ℂ) - U * I)) * logDeriv poleFactor s)
      ((a : ℂ) - U * I) ((2 : ℂ) + U * I) = 1 - ((a : ℂ) - U * I) := by
  let z : ℂ := (a : ℂ) - U * I
  let w : ℂ := (2 : ℂ) + U * I
  have hb := poleFactor_boundary ha hU
  have hr : z.re ≤ w.re := by simp [z, w]; linarith
  have hi : z.im ≤ w.im := by simp [z, w]; linarith
  have hp : Rectangle z w ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hr, uIoo_of_le hi, mem_reProdIm]
    simp [z, w, ha, hU, neg_lt_zero.mpr hU]
  have he : EqOn (fun s => (s - z) * logDeriv poleFactor s)
      ((fun _ : ℂ => (1 : ℂ)) + fun s => (1 - z) / (s - 1)) (RectangleBorder z w) := by
    intro s hs
    have hn : s - 1 ≠ 0 := hb s hs
    have hd : deriv poleFactor s = 1 := by
      change deriv (fun s : ℂ => s - 1) s = 1
      exact ((hasDerivAt_id s).sub_const 1).deriv
    simp only [Pi.add_apply, logDeriv_apply, hd, poleFactor]
    field_simp
    ring
  have hconst : RectangleBorderIntegrable (fun _ : ℂ => (1 : ℂ)) z w :=
    ContinuousOn.rectangleBorderIntegrable continuousOn_const
  have hrat : RectangleBorderIntegrable (fun s => (1 - z) / (s - 1)) z w :=
    ContinuousOn.rectangleBorder_integrable (fun s hs =>
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (hb s hs)).continuousWithinAt)
  rw [RectangleIntegral'_congr he, RectangleIntegral', hconst.add hrat, smul_add]
  have hzero : RectangleIntegral (fun _ : ℂ => (1 : ℂ)) z w = 0 := by
    simp [RectangleIntegral, HIntegral, VIntegral]
  rw [hzero, smul_zero, zero_add]
  exact ResidueTheoremInRectangle hr hi hp

theorem poleFactor_littlewood {a U : ℝ} (ha : a < 1) (hU : 0 < U) :
    2 * Real.pi * (1 - a) =
      (∫ t in -U..U, Real.log ‖poleFactor ((a : ℂ) + t * I)‖) -
        (∫ t in -U..U, Real.log ‖poleFactor ((2 : ℂ) + t * I)‖) +
          (∫ x in a..2, (horizontalLog poleFactor 2 U U x).im) -
            (∫ x in a..2, (horizontalLog poleFactor 2 U (-U) x).im) := by
  have h := rectangle_littlewood_entire poleFactor_differentiable (a := a) (b := 2)
    (c := -U) (d := U) (by simpa [sub_eq_add_neg] using poleFactor_boundary ha hU)
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg, ofReal_ofNat] at h
  rw [poleFactor_weighted_contour ha hU] at h
  simpa using h

theorem log_entireH_split {y : ℝ} {s : ℂ} (hs : s ≠ 1) (hn : entireH y s ≠ 0) :
    Real.log ‖entireH y s‖ = Real.log ‖H y s‖ + 2 * Real.log ‖poleFactor s‖ := by
  have hnH : H y s ≠ 0 := by
    intro hz
    apply hn
    rw [entireH_eq hs, hz, mul_zero]
  rw [entireH_eq hs, norm_mul, norm_pow,
    Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs)))
      (norm_ne_zero_iff.mpr hnH), Real.log_pow]
  simp only [poleFactor]
  ring

def HhorizontalLog (y b d h x : ℝ) : ℂ :=
  horizontalLog (entireH y) b d h x - 2 * horizontalLog poleFactor b d h x

theorem HhorizontalLog_exp {y a U h x : ℝ} (ha : a < 1) (hU : 0 < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0)
    (hh : h = -U ∨ h = U) (hx : x ∈ [[a, 2]]) :
    Complex.exp (HhorizontalLog y 2 U h x) = H y ((x : ℂ) + h * I) := by
  have hne : ∀ s ∈ RectangleBorder ((a : ℂ) + (-U : ℝ) * I) ((2 : ℂ) + U * I),
      entireH y s ≠ 0 := by simpa [sub_eq_add_neg] using hn
  have hnp : ∀ s ∈ RectangleBorder ((a : ℂ) + (-U : ℝ) * I) ((2 : ℂ) + U * I),
      poleFactor s ≠ 0 := by simpa [sub_eq_add_neg] using poleFactor_boundary ha hU
  obtain ⟨ec, ed, _, eb⟩ := rectangle_nonzero_lines hne
  obtain ⟨pc, pd, _, pb⟩ := rectangle_nonzero_lines hnp
  have hm : h ∈ [[-U, U]] := hh.elim (fun he => he ▸ left_mem_uIcc) (fun he => he ▸ right_mem_uIcc)
  have eh := horizontalLog_exp (differentiable_entireH y) eb hm
    (hh.elim (fun he => he ▸ ec) (fun he => he ▸ ed)) hx
  have ph := horizontalLog_exp poleFactor_differentiable pb hm
    (hh.elim (fun he => he ▸ pc) (fun he => he ▸ pd)) hx
  norm_num only [Nat.cast_ofNat] at eh ph
  have ps : poleFactor ((x : ℂ) + h * I) ≠ 0 :=
    hh.elim (fun he => he ▸ pc x hx) (fun he => he ▸ pd x hx)
  have hexp : Complex.exp (2 * horizontalLog poleFactor 2 U h x) =
      Complex.exp (horizontalLog poleFactor 2 U h x) ^ 2 := by
    exact Complex.exp_nat_mul _ 2
  rw [HhorizontalLog, Complex.exp_sub, hexp, eh, ph,
    entireH_eq (sub_ne_zero.mp ps)]
  change (poleFactor ((x : ℂ) + h * I) ^ 2 * H y ((x : ℂ) + h * I)) /
    (poleFactor ((x : ℂ) + h * I) ^ 2) = _
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 ps)

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
