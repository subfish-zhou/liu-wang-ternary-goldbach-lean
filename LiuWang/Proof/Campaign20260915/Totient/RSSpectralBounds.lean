import LiuWang.Proof.Campaign20260915.Totient.RSHigherSpectrum
import LiuWang.Proof.Campaign20260915.Totient.RSGammaBounds
import LiuWang.Proof.Campaign20260915.Totient.RSZeroBackward
import LiuWang.Proof.Campaign20260915.Totient.RSParameters

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_difference_sub {E : Type*} [AddCommGroup E]
    (f g : ℝ → E) (h : ℝ) (m : ℕ) (x : ℝ) :
    (fwdDiff h)^[m] (fun t => f t - g t) x =
      (fwdDiff h)^[m] f x - (fwdDiff h)^[m] g x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply', fwdDiff, ih]; abel

theorem rs_factorial_power_difference (m : ℕ) (h x : ℝ) :
    (fwdDiff h)^[m] (fun t : ℝ => t ^ m / m.factorial) x = h ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    change (fwdDiff h)^[m + 1] (rsMainPrimitive m) x = _
    rw [Function.iterate_succ_apply']
    simp only [fwdDiff, rsMainPrimitive_finite_difference]
    rw [pow_succ]
    ring

theorem rsPolePrimitive_finite_difference (m : ℕ) (h x : ℝ) :
    (fwdDiff h)^[m] (rsPolePrimitive m) x =
      h ^ m * (x + (m : ℝ) * h / 2 - Real.log (2 * Real.pi)) := by
  have he : rsPolePrimitive m = fun t => rsMainPrimitive m t -
      (Real.log (2 * Real.pi) • (fun y : ℝ => y ^ m / m.factorial)) t := by
    funext t
    simp only [rsPolePrimitive, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  rw [he, rs_difference_sub, fwdDiff_iter_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, rs_factorial_power_difference,
    rsMainPrimitive_finite_difference]
  ring

theorem rsPsiPrimitive_real_spectrum {m : ℕ} (hm : 1 ≤ m)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 1 < x) :
    (fwdDiff h)^[m] (rsPsiPrimitive m) x =
      h ^ m * (x + (m : ℝ) * h / 2 - Real.log (2 * Real.pi)) -
        ((fwdDiff h)^[m] (fun t => ∑' p, rsZeroPrimitive m t p) x).re +
          ((fwdDiff h)^[m] (rsGammaPrimitive m) x).re := by
  have he := rsPsiPrimitive_spectral_difference hm hh hx
  have he' :
      (fwdDiff h)^[m] (fun t => (rsPsiPrimitive m t : ℂ)) x =
        (fwdDiff h)^[m] ((fun t => (rsPolePrimitive m t : ℂ) -
          ∑' p, rsZeroPrimitive m t p) + rsGammaPrimitive m) x := he
  rw [fwdDiff_iter_add, Pi.add_apply, rs_difference_sub,
    rs_difference_ofReal, rs_difference_ofReal] at he'
  have hr := congrArg Complex.re he'
  simpa only [Complex.ofReal_re, Complex.add_re, Complex.sub_re,
    rsPolePrimitive_finite_difference] using hr

theorem rsPsiPrimitive_normalized_spectral_bounds {m : ℕ} (hm : 1 ≤ m)
    {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    x + (m : ℝ) * h / 2 - Real.log (2 * Real.pi) -
        ‖(fwdDiff h)^[m] (fun t => ∑' p, rsZeroPrimitive m t p) x‖ / h ^ m ≤
      (fwdDiff h)^[m] (rsPsiPrimitive m) x / h ^ m ∧
    (fwdDiff h)^[m] (rsPsiPrimitive m) x / h ^ m ≤
      x + (m : ℝ) * h / 2 - Real.log (2 * Real.pi) +
        ‖(fwdDiff h)^[m] (fun t => ∑' p, rsZeroPrimitive m t p) x‖ / h ^ m +
          rsTrivialKernel x := by
  have hg := rsGammaPrimitive_normalized_bounds hm hh hx
  have hz := Complex.abs_re_le_norm
    ((fwdDiff h)^[m] (fun t => ∑' p, rsZeroPrimitive m t p) x)
  have hz' := (abs_le.mp hz)
  have hl := div_le_div_of_nonneg_right hz'.1 (pow_pos hh m).le
  have hu := div_le_div_of_nonneg_right hz'.2 (pow_pos hh m).le
  simp only [neg_div] at hl
  rw [rsPsiPrimitive_real_spectrum hm hh.le hx, add_div, sub_div,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hh.ne')]
  constructor <;> linarith

theorem rsPsi_original_moment_bounds {m : ℕ} (hm : 1 ≤ m)
    {δ a x : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hcut : 1 + (m : ℝ) * δ * a < a) (hax : a ≤ x) :
    x - (m : ℝ) * δ * x / 2 -
        x * 2 ^ m / δ ^ m * (∑' p, rsZeroMoment m (Real.log x) p) - 1.84 <
      Chebyshev.psi x ∧
    Chebyshev.psi x <
      x + (m : ℝ) * δ * x / 2 +
        x * (1 + (1 + δ) ^ (m + 1)) ^ m / δ ^ m *
          (∑' p, rsZeroMoment m (Real.log x) p) + rsTrivialKernel x := by
  have hx0 : 0 < x := ha.trans_le hax
  have hh : 0 < δ * x := mul_pos hδ hx0
  obtain ⟨hleft, hlo, hhi⟩ := rsPsiPrimitive_original_desmoothing hδ ha hcut hax
  have hmh : 0 ≤ (m : ℝ) * (δ * x) := mul_nonneg (Nat.cast_nonneg m) hh.le
  have hx : 1 < x := by linarith
  have hl := (rsPsiPrimitive_normalized_spectral_bounds hm hh hleft).1
  have hu := (rsPsiPrimitive_normalized_spectral_bounds hm hh hx).2
  have hzlo := rsZeroPrimitive_original_backward hm hδ ha hcut hax
  have hzhi := rsZeroPrimitive_normalized_difference_bound hm hx.le hδ
  have hc := rs_log_two_pi_interval
  constructor <;> nlinarith

#print axioms rs_difference_sub
#print axioms rs_factorial_power_difference
#print axioms rsPolePrimitive_finite_difference
#print axioms rsPsiPrimitive_real_spectrum
#print axioms rsPsiPrimitive_normalized_spectral_bounds
#print axioms rsPsi_original_moment_bounds

end LiuWang.Proof.Campaign20260915.Totient
