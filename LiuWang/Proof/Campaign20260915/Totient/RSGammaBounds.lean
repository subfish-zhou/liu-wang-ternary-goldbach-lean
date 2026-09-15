import LiuWang.Proof.Campaign20260915.Totient.RSLocalDifferences

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rsTrivialKernel_integrable {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable rsTrivialKernel volume a b :=
  (rsTrivialKernel_antitone.mono (fun _ ht => (lt_min ha hb).trans_le ht.1)).intervalIntegrable

theorem rsGammaPrimitive_real_integrable (m : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => (rsGammaPrimitive m t).re) volume a b := by
  have hi := rsGammaPrimitive_integrable m ha hb
  exact ⟨hi.1.re, hi.2.re⟩

theorem rsGammaCorrection_difference {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) :
    fwdDiff h (fun t => (gammaCorrection t).re) x =
      ∫ t in (0 : ℝ)..h, rsTrivialKernel (x + t) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := x) (b := x + h)
    (fun t ht => rsGammaCorrection_deriv
      (hx.trans_le (by simpa only [min_eq_left (by linarith : x ≤ x + h)] using ht.1)))
    (by
      have hi := rsTrivialKernel_integrable hx (by linarith : 1 < x + h)
      exact ⟨hi.1.ofReal, hi.2.ofReal⟩)
  rw [intervalIntegral.integral_ofReal] at he
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.sub_re] at hr
  rw [intervalIntegral.integral_comp_add_left, add_zero]
  exact hr.symm

theorem rsGammaPrimitive_real_difference {m : ℕ} (hm : 1 ≤ m)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) :
    fwdDiff h (fun t => (rsGammaPrimitive (m + 1) t).re) x =
      ∫ t in (0 : ℝ)..h, (rsGammaPrimitive m (x + t)).re := by
  have hre : (∫ t in x..x + h, (rsGammaPrimitive m t).re) =
      (∫ t in x..x + h, rsGammaPrimitive m t).re :=
    Complex.reCLM.intervalIntegral_comp_comm
      (rsGammaPrimitive_integrable m hx (by linarith : 1 < x + h))
  rw [intervalIntegral.integral_comp_add_left (fun y => (rsGammaPrimitive m y).re) x,
    add_zero, hre]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (rsGammaPrimitive_integrable m (by norm_num : (1 : ℝ) < 2) hx)
    (rsGammaPrimitive_integrable m hx (by linarith : 1 < x + h))
  rw [rsGammaPrimitive_integral hm, rsGammaPrimitive_integral hm] at hi
  have hr := congrArg Complex.re hi
  simp only [Complex.add_re] at hr
  change (rsGammaPrimitive (m + 1) (x + h)).re - (rsGammaPrimitive (m + 1) x).re = _
  linarith

theorem rsGammaPrimitive_difference_bounds {m : ℕ} (hm : 1 ≤ m)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) :
    0 ≤ ((fwdDiff h)^[m] (rsGammaPrimitive m) x).re ∧
      ((fwdDiff h)^[m] (rsGammaPrimitive m) x).re ≤ h ^ m * rsTrivialKernel x := by
  rw [← rs_difference_re]
  induction m, hm using Nat.le_induction generalizing x with
  | base =>
    simp only [Function.iterate_one, rsGammaPrimitive, pow_one]
    rw [rsGammaCorrection_difference hh hx]
    have hi : IntervalIntegrable (fun t => rsTrivialKernel (x + t)) volume 0 h := by
      simpa only [add_sub_cancel_right, sub_self] using
        (rsTrivialKernel_integrable hx (by linarith : 1 < h + x)).comp_add_left x
    constructor
    · exact intervalIntegral.integral_nonneg hh (fun t ht =>
        rsTrivialKernel_nonneg (by linarith [ht.1]))
    · have hu := intervalIntegral.integral_mono_on hh hi intervalIntegrable_const
        (fun t ht => rsTrivialKernel_antitone hx (by linarith [ht.1] : 1 < x + t)
          (by linarith [ht.1]))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hu
  | succ m hm ih =>
    rw [Function.iterate_succ_apply,
      rs_difference_congr_positive (fun y hy => rsGammaPrimitive_real_difference hm hh hy) hh hx,
      rs_local_difference_integral
        (fun a b ha hb => rsGammaPrimitive_real_integrable m ha hb) hh hx]
    have hi : IntervalIntegrable
        (fun t => (fwdDiff h)^[m] (fun y => (rsGammaPrimitive m y).re) (x + t)) volume 0 h := by
      simpa only [add_sub_cancel_right, sub_self] using
        (rs_local_difference_integrable
          (fun a b ha hb => rsGammaPrimitive_real_integrable m ha hb) hh m hx
          (by linarith : 1 < h + x)).comp_add_left x
    constructor
    · exact intervalIntegral.integral_nonneg hh (fun t ht => (ih (by linarith [ht.1])).1)
    · have hu := intervalIntegral.integral_mono_on hh hi intervalIntegrable_const
        (fun t ht => (ih (by linarith [ht.1] : 1 < x + t)).2.trans
          (mul_le_mul_of_nonneg_left
            (rsTrivialKernel_antitone hx (by linarith [ht.1] : 1 < x + t) (by linarith [ht.1]))
            (pow_nonneg hh m)))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, pow_succ,
        mul_left_comm, mul_assoc, mul_comm] using hu

theorem rsGammaPrimitive_normalized_bounds {m : ℕ} (hm : 1 ≤ m)
    {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    0 ≤ ((fwdDiff h)^[m] (rsGammaPrimitive m) x).re / h ^ m ∧
      ((fwdDiff h)^[m] (rsGammaPrimitive m) x).re / h ^ m ≤ rsTrivialKernel x := by
  have hb := rsGammaPrimitive_difference_bounds hm hh.le hx
  exact ⟨div_nonneg hb.1 (pow_pos hh m).le,
    (div_le_iff₀ (pow_pos hh m)).mpr (by simpa [mul_comm] using hb.2)⟩

#print axioms rsTrivialKernel_integrable
#print axioms rsGammaCorrection_difference
#print axioms rsGammaPrimitive_real_difference
#print axioms rsGammaPrimitive_difference_bounds
#print axioms rsGammaPrimitive_normalized_bounds

end LiuWang.Proof.Campaign20260915.Totient
