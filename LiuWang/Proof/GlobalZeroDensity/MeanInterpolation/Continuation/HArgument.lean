import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ArgumentVariation

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped Interval ComplexConjugate

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def reflectedZeros (y U r : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r)).finiteSupport
    (isCompact_closedBall (2 : ℂ) r)).toFinset

theorem mem_reflectedZeros_of_zero {y U r : ℝ} (hy : 5 ≤ y)
    (hr : 0 ≤ r) (hrU : r < U) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) r)
    (hz : reflectedH y U s = 0) : s ∈ reflectedZeros y U r := by
  have hA := reflectedH_analytic (y := y) hrU
  have ho := (hA s hs).analyticOrderAt_eq_zero
  rw [← Nat.cast_analyticOrderNatAt (reflectedH_order_finite hy hr hrU hs)] at ho
  simp only [Nat.cast_eq_zero] at ho
  have hn : analyticOrderNatAt (reflectedH y U) s ≠ 0 := fun h => (ho.mp h) hz
  apply ((MeromorphicOn.divisor (reflectedH y U) (closedBall (2 : ℂ) r)).finiteSupport
    (isCompact_closedBall (2 : ℂ) r)).mem_toFinset.mpr
  rw [Function.mem_support, reflectedH_divisor_actual_order hy hr le_rfl hrU hs]
  exact_mod_cast hn

theorem horizontal_real_zero_reflected {y U h x : ℝ} (hh : h = -U ∨ h = U)
    (hz : (H y ((x : ℂ) + h * I)).re = 0) : reflectedH y U x = 0 := by
  apply (reflectedH_real_zero_iff y U x).mpr
  rcases hh with rfl | rfl
  · have he : (x : ℂ) + (-U : ℝ) * I = conj ((x : ℂ) + U * I) := by simp
    rw [he, H_conj, conj_re] at hz
    exact hz
  · exact hz

theorem horizontal_argument_variation {y a U h x : ℝ} (hy : 5 ≤ y)
    (ha : a < 1) (hU : 0 < U) (hrU : 2 - a < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0)
    (hh : h = -U ∨ h = U) (hx : x ∈ Icc a 2) :
    |(HhorizontalLog y 2 U h x).im - (HhorizontalLog y 2 U h 2).im| ≤
      ((reflectedZeros y U (2 - a)).card + 1 : ℝ) * Real.pi := by
  have ha2 : a ≤ 2 := by linarith
  have hA : ContinuousOn (fun t : ℝ => (HhorizontalLog y 2 U h t).im) (Icc a 2) := by
    simpa only [uIcc_of_le ha2, Function.comp_def] using
      Complex.continuous_im.comp_continuousOn (HhorizontalLog_continuousOn ha hU hn hh)
  have hS : ∀ t ∈ Icc a 2, Real.cos (HhorizontalLog y 2 U h t).im = 0 →
      (t : ℂ) ∈ reflectedZeros y U (2 - a) := by
    intro t ht hc
    have he := congrArg Complex.re (HhorizontalLog_exp ha hU hn hh
      (by simpa [uIcc_of_le ha2] using ht))
    rw [Complex.exp_re, hc, mul_zero] at he
    have hz := horizontal_real_zero_reflected hh he.symm
    have hd : (t : ℂ) ∈ closedBall (2 : ℂ) (2 - a) := by
      rw [mem_closedBall_iff_norm]
      have heq : (t : ℂ) - 2 = ((t - 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0)]
      linarith [ht.1]
    exact mem_reflectedZeros_of_zero hy (by linarith) hrU hd hz
  have hv := argument_variation_le hx.2
    (hA.mono (Icc_subset_Icc hx.1 le_rfl)) (reflectedZeros y U (2 - a))
    (fun t ht => hS t (Icc_subset_Icc hx.1 le_rfl ht))
  simpa only [abs_sub_comm] using hv

theorem horizontal_argument_centered_integral {y a U h : ℝ} (hy : 5 ≤ y)
    (ha : a < 1) (hU : 0 < U) (hrU : 2 - a < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0)
    (hh : h = -U ∨ h = U) :
    |HargIntegral y a U h - (2 - a) * (HhorizontalLog y 2 U h 2).im| ≤
      (2 - a) * (((reflectedZeros y U (2 - a)).card + 1 : ℝ) * Real.pi) := by
  have hi := (HargIntegral_split ha hU hn hh).1
  have ha2 : a ≤ 2 := by linarith
  have he : HargIntegral y a U h - (2 - a) * (HhorizontalLog y 2 U h 2).im =
      ∫ x in a..2, (HhorizontalLog y 2 U h x).im - (HhorizontalLog y 2 U h 2).im := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
    rfl
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := 2)
    (f := fun x : ℝ => (HhorizontalLog y 2 U h x).im - (HhorizontalLog y 2 U h 2).im)
    (C := (((reflectedZeros y U (2 - a)).card + 1 : ℝ) * Real.pi))
    (fun x hx => by
      have hx' : x ∈ Icc a 2 := by
        simpa [uIcc_of_le ha2] using (uIoc_subset_uIcc hx)
      simpa only [Real.norm_eq_abs] using
        horizontal_argument_variation hy ha hU hrU hn hh hx')
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha2), mul_comm] using hb

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
