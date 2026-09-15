import LiuWang.Proof.DirichletZeroCount.Remainder.LogGamma
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Signed trapezoidal error for the imaginary part of the right-half-plane log -/

set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory
open scoped Topology

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem convex_cell_integral {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    (hc : ContinuousOn f (Set.Ici 0)) (n : ℕ) :
    (∫ t in (n : ℝ)..(n + 1 : ℕ), f t) ≤ (f n + f (n + 1 : ℕ)) / 2 := by
  have hfc : ContinuousOn (fun t : ℝ => f ((n : ℝ) + t)) (Set.uIcc 0 1) := by
    apply hc.comp (by fun_prop)
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact add_nonneg (Nat.cast_nonneg n) ht.1
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      f ((n : ℝ) + t) ≤ (1 - t) * f n + t * f (n + 1 : ℕ) := by
    have h := hf.2 (show (n : ℝ) ∈ Set.Ici (0 : ℝ) from by
        exact Nat.cast_nonneg (α := ℝ) n)
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ici 0 from by
        change (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
        positivity)
      (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
    convert! h using 1
    congr 1
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have he := intervalIntegral.integral_mono_on (μ := volume) zero_le_one hfc.intervalIntegrable
    ((show Continuous (fun t : ℝ => (1 - t) * f n + t * f (n + 1 : ℕ)) by fun_prop).intervalIntegrable 0 1) hp
  have hi : (∫ t in (0 : ℝ)..1, (1 - t) * f n + t * f (n + 1 : ℕ)) =
      (f n + f (n + 1 : ℕ)) / 2 := by
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x) intervalIntegrable_const
        (Continuous.intervalIntegrable continuous_id 0 1)]
    norm_num [integral_id]
    ring
  rw [hi] at he
  have hshift := intervalIntegral.integral_comp_add_left f (a := 0) (b := 1) (n : ℝ)
  simpa only [hshift, add_zero, Nat.cast_add, Nat.cast_one] using he

theorem convex_sum_ge_integral {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    (hc : ContinuousOn f (Set.Ici 0)) (n : ℕ) :
    (∫ t in (0 : ℝ)..n, f t) + (f 0 + f n) / 2 ≤
      ∑ m ∈ Finset.range (n + 1), f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcell := convex_cell_integral hf hc n
    have hi (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
        IntervalIntegrable f volume a b :=
      (hc.mono (fun x hx => (le_min ha hb).trans hx.1)).intervalIntegrable
    rw [Finset.sum_range_succ]
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by simp]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hi 0 n le_rfl (Nat.cast_nonneg n))
      (hi n (n + 1) (Nat.cast_nonneg n) (by positivity))]
    push_cast at hcell ⊢
    linarith

theorem phase_hasDerivAt {z : ℂ} {x : ℝ} (hx : 0 < (z + (x : ℂ)).re) :
    HasDerivAt (fun t : ℝ => (log (z + (t : ℂ))).im)
      (-z.im / ((z.re + x) ^ 2 + z.im ^ 2)) x := by
  have hs : z + (x : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hx)
  have hd := (hasDerivAt_log hs).scomp x (Complex.ofRealCLM.hasDerivAt.const_add z)
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [Function.comp_def, smul_eq_mul, Complex.inv_im, Complex.normSq_apply, pow_two] using! hi

theorem phase_convex {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (log (z + (x : ℂ))).im) := by
  have hd (x : ℝ) (hx : x ∈ Set.Ici (0 : ℝ)) :=
    phase_hasDerivAt (z := z) (x := x)
      (by simp only [add_re, ofReal_re]; exact add_pos_of_pos_of_nonneg hz hx)
  have hc : ContinuousOn (fun x : ℝ => (log (z + (x : ℂ))).im) (Set.Ici 0) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) hc
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(hd x (interior_subset hx)).deriv, (hd y (interior_subset hy)).deriv]
  have hx0 : 0 ≤ x := interior_subset hx
  have hy0 : 0 ≤ y := interior_subset hy
  have hdx : 0 < (z.re + x) ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  have hden : (z.re + x) ^ 2 + z.im ^ 2 ≤ (z.re + y) ^ 2 + z.im ^ 2 := by
    nlinarith
  simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_left ht hdx hden)

theorem phase_primitive {z : ℂ} {x : ℝ} (hx : 0 < (z + (x : ℂ)).re) :
    HasDerivAt (fun t : ℝ => ((z + (t : ℂ)) * log (z + (t : ℂ)) - (z + (t : ℂ))).im)
      (log (z + (x : ℂ))).im x := by
  have hs : z + (x : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hx)
  have hn : z + (x : ℂ) ≠ 0 := by intro h; simp [h] at hx
  have hline := Complex.ofRealCLM.hasDerivAt.const_add z (x := x)
  have hd := ((hline.mul ((hasDerivAt_log hs).scomp x hline)).sub hline)
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa [Function.comp_def, smul_eq_mul, hn] using! hi

theorem integral_phase {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    (∫ x in (0 : ℝ)..n, (log (z + (x : ℂ))).im) =
      ((z + n) * log (z + n) - (z + n)).im - (z * log z - z).im := by
  have hp (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) n) : 0 < (z + (x : ℂ)).re := by
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)] at hx
    simp only [add_re, ofReal_re]
    linarith [hx.1]
  have hi : IntervalIntegrable (fun x : ℝ => (log (z + (x : ℂ))).im) volume 0 n :=
    (show ContinuousOn _ (Set.uIcc (0 : ℝ) n) from
      fun x hx => (phase_hasDerivAt (hp x hx)).continuousAt.continuousWithinAt).intervalIntegrable
  simpa only [ofReal_zero, add_zero, ofReal_natCast] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => phase_primitive (hp x hx)) hi

def stirlingPhase (z : ℂ) : ℝ := ((z - 1 / 2) * log z - z).im

def phaseTail (z : ℂ) (n : ℕ) : ℝ :=
  (z * (Real.log n : ℂ) - (z + n + 1 / 2) * log (z + n) + (z + n)).im

theorem logGammaSeq_im_le {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) (n : ℕ) :
    (logGammaSeq z n).im ≤ stirlingPhase z + phaseTail z n := by
  have hc : ContinuousOn (fun x : ℝ => (log (z + (x : ℂ))).im) (Set.Ici 0) := by
    intro x hx
    exact (phase_hasDerivAt (z := z) (x := x)
      (by simp only [add_re, ofReal_re]; exact add_pos_of_pos_of_nonneg hz hx)).continuousAt.continuousWithinAt
  have h := convex_sum_ge_integral (phase_convex hz ht) hc n
  rw [integral_phase hz] at h
  simp only [ofReal_zero, add_zero, ofReal_natCast] at h
  simp only [logGammaSeq, stirlingPhase, phaseTail, sub_im, add_im, mul_im,
    ofReal_re, ofReal_im, mul_zero, zero_add, Complex.im_sum] at h ⊢
  norm_num at h ⊢
  linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
