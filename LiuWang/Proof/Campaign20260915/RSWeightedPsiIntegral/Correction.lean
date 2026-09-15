import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.TrivialTail

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open LiuWang.Proof.Campaign20260915.Totient

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def lemma8Factor (x : ℝ) : ℝ := (2 + Real.log x) / Real.log x ^ 2

def signedCorrection (y : ℝ) : ℝ := (Real.log (2 * Real.pi) - rsTrivialKernel y) * weight y

theorem scaledWeight_antitone : AntitoneOn scaledWeight (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  rw [scaledWeight_eq hx, scaledWeight_eq hy]
  have hi := inv_anti₀ (Real.log_pos hx) (Real.log_le_log (by linarith : 0 < x) hxy)
  exact add_le_add (pow_le_pow_left₀ (inv_nonneg.mpr (Real.log_pos hy).le) hi 2) hi

theorem lemma8Factor_pos {x : ℝ} (hx : 1 < x) : 0 < lemma8Factor x := by
  have hl := Real.log_pos hx
  unfold lemma8Factor
  positivity

theorem scaledWeight_le_lemma8Factor {x : ℝ} (_hx : 1 < x) :
    scaledWeight x ≤ lemma8Factor x := by
  unfold scaledWeight lemma8Factor
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem trivialKernel_weight_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun y => rsTrivialKernel y * weight y) (Ioi x) := by
  refine ((weight_integrableOn hx).const_mul (rsTrivialKernel x)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold rsTrivialKernel weight; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (rsTrivialKernel_nonneg (hx.trans hy)) (weight_nonneg (hx.trans hy)))]
  exact mul_le_mul_of_nonneg_right
    (rsTrivialKernel_antitone hx (hx.trans hy) hy.le) (weight_nonneg (hx.trans hy))

theorem trivialKernel_weight_integral_lt {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, rsTrivialKernel y * weight y) <
      lemma8Factor x * ((31 / 100 : ℝ) / x ^ 3) := by
  have h := integral_mono_ae (trivialKernel_weight_integrable hx)
    ((trivialKernel_div_sq_integrable hx).const_mul (lemma8Factor x))
    (show ∀ᵐ y ∂volume.restrict (Ioi x),
      rsTrivialKernel y * weight y ≤ lemma8Factor x * (rsTrivialKernel y / y ^ 2) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [weight_eq_scaled]
      calc
        _ = scaledWeight y * (rsTrivialKernel y / y ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          ((scaledWeight_antitone hx (hx.trans hy) hy.le).trans
            (scaledWeight_le_lemma8Factor hx))
          (div_nonneg (rsTrivialKernel_nonneg (hx.trans hy)) (sq_nonneg y)))
  rw [integral_const_mul] at h
  exact h.trans_lt (mul_lt_mul_of_pos_left (trivialKernel_div_sq_integral_lt hx)
    (lemma8Factor_pos hx))

theorem constant_weight_integral_lt {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, Real.log (2 * Real.pi) * weight y) <
      lemma8Factor x * ((184 / 100 : ℝ) / x) := by
  rw [integral_const_mul, weight_integral_Ioi hx]
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hc : Real.log (2 * Real.pi) < (184 / 100 : ℝ) :=
    lt_of_le_of_lt rs_log_two_pi_interval.2 (by norm_num)
  calc
    _ < (184 / 100 : ℝ) * (1 / (x * Real.log x)) :=
      mul_lt_mul_of_pos_right hc (by positivity)
    _ ≤ lemma8Factor x * ((184 / 100 : ℝ) / x) := by
      unfold lemma8Factor
      field_simp
      nlinarith

theorem signedCorrection_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn signedCorrection (Ioi x) := by
  have h := ((weight_integrableOn hx).const_mul (Real.log (2 * Real.pi))).sub
    (trivialKernel_weight_integrable hx)
  exact h.congr (Filter.Eventually.of_forall (fun y => by
    dsimp [signedCorrection]
    ring))

theorem signedCorrection_integral_abs_lt {x : ℝ} (hx : 1 < x) :
    |∫ y in Ioi x, signedCorrection y| <
      lemma8Factor x * ((184 / 100 : ℝ) / x + (31 / 100 : ℝ) / x ^ 3) := by
  have hc := ((weight_integrableOn hx).const_mul (Real.log (2 * Real.pi)))
  have ht := trivialKernel_weight_integrable hx
  have h := integral_mono_ae (signedCorrection_integrable hx).norm (hc.add ht)
    (show ∀ᵐ y ∂volume.restrict (Ioi x), ‖signedCorrection y‖ ≤
      Real.log (2 * Real.pi) * weight y + rsTrivialKernel y * weight y from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hw := weight_nonneg (hx.trans hy)
      have hg := rsTrivialKernel_nonneg (hx.trans hy)
      have hl : 0 ≤ Real.log (2 * Real.pi) := by linarith [rs_log_two_pi_interval.1]
      dsimp [signedCorrection]
      rw [abs_mul, abs_of_nonneg hw]
      exact (mul_le_mul_of_nonneg_right
        (abs_sub_le (Real.log (2 * Real.pi)) 0 (rsTrivialKernel y)) hw).trans_eq (by
        rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg hl, abs_of_nonneg hg]
        ring))
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Ioi x)) signedCorrection
  rw [Real.norm_eq_abs] at hn
  simp only [Pi.add_apply] at h
  rw [integral_add hc ht] at h
  apply (hn.trans h).trans_lt
  have hb := add_lt_add (constant_weight_integral_lt hx) (trivialKernel_weight_integral_lt hx)
  simpa only [mul_add] using hb

#print axioms signedCorrection_integrable
#print axioms signedCorrection_integral_abs_lt

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
