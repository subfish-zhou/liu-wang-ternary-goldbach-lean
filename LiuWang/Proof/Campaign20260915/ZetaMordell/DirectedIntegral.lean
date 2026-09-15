import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

-- The positive quadratic phase decays on the southwest-to-northeast line.
def mordellLine (t : ℝ) : ℂ := 1 / 2 + (1 + I) * t

def mordellDenominator (t : ℝ) : ℂ :=
  exp (2 * Real.pi * I * mordellLine t) - 1

def mordellGaussian (a : ℂ) (t : ℝ) : ℂ :=
  exp (Real.pi * I * mordellLine t ^ 2 + 2 * Real.pi * I * a * mordellLine t)

def mordellKernel (a : ℂ) (t : ℝ) : ℂ :=
  mordellGaussian a t / mordellDenominator t * (1 + I)

def mordellIntegral (a : ℂ) : ℂ := ∫ t : ℝ, mordellKernel a t

theorem mordellLine_hasDerivAt (t : ℝ) :
    HasDerivAt mordellLine (1 + I) t := by
  change HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + (1 + I) * t) (1 + I) t
  simpa using
    ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (1 + I)).const_add (1 / 2 : ℂ)

theorem mordellDenominator_exp_norm (t : ℝ) :
    ‖exp (2 * Real.pi * I * mordellLine t)‖ = Real.exp (-2 * Real.pi * t) := by
  rw [norm_exp]
  congr 1
  simp [mordellLine, mul_re, mul_im]

theorem mordellDenominator_ne_zero (t : ℝ) : mordellDenominator t ≠ 0 := by
  intro h
  have he : exp (2 * Real.pi * I * mordellLine t) = 1 := sub_eq_zero.mp h
  have hn := congrArg norm he
  rw [mordellDenominator_exp_norm, norm_one, Real.exp_eq_one_iff] at hn
  have ht : t = 0 := by nlinarith [Real.pi_pos]
  subst t
  have hp : 2 * (Real.pi : ℂ) * I * mordellLine 0 = Real.pi * I := by
    norm_num [mordellLine]
    ring
  rw [hp, Complex.exp_pi_mul_I] at he
  norm_num at he

theorem mordellDenominator_inv_continuous :
    Continuous (fun t : ℝ => (mordellDenominator t)⁻¹) := by
  apply Continuous.inv₀
  · unfold mordellDenominator mordellLine
    fun_prop
  · exact mordellDenominator_ne_zero

theorem mordellDenominator_inv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖(mordellDenominator t)⁻¹‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (mordellDenominator_inv_continuous.norm.continuousOn :
      ContinuousOn (fun t : ℝ => ‖(mordellDenominator t)⁻¹‖) (Icc (-1) 1))
  refine ⟨max C 2, le_trans (by norm_num) (le_max_right _ _), fun t => ?_⟩
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · exact (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hlow : 1 / 2 ≤ ‖mordellDenominator t‖ := by
    rcases lt_or_gt_of_ne (show t ≠ 0 by intro h; simp [h] at ht) with hn | hp
    · have ht' : t < -1 := by simp only [mem_Icc, not_and_or, not_le] at ht; rcases ht with h | h <;> linarith
      have he := Real.add_one_le_exp (-2 * Real.pi * t)
      have hr := norm_sub_norm_le (exp (2 * Real.pi * I * mordellLine t)) (1 : ℂ)
      rw [mordellDenominator_exp_norm, norm_one] at hr
      change Real.exp (-2 * Real.pi * t) - 1 ≤ ‖mordellDenominator t‖ at hr
      nlinarith [Real.two_le_pi]
    · have ht' : 1 < t := by simp only [mem_Icc, not_and_or, not_le] at ht; rcases ht with h | h <;> linarith
      have he : 2 ≤ Real.exp (2 * Real.pi * t) := by
        have := Real.add_one_le_exp (2 * Real.pi * t)
        nlinarith [Real.two_le_pi]
      have hi : Real.exp (-2 * Real.pi * t) ≤ 1 / 2 := by
        rw [show -2 * Real.pi * t = -(2 * Real.pi * t) by ring, Real.exp_neg]
        exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
          (by norm_num; exact he)
      have hr := norm_sub_norm_le (1 : ℂ) (exp (2 * Real.pi * I * mordellLine t))
      rw [norm_one, mordellDenominator_exp_norm, norm_sub_rev] at hr
      change 1 - Real.exp (-2 * Real.pi * t) ≤ ‖mordellDenominator t‖ at hr
      linarith
  apply le_trans _ (le_max_right C 2)
  rw [norm_inv]
  exact (inv_le_comm₀ (lt_of_lt_of_le (by norm_num) hlow) (by norm_num : (0 : ℝ) < 2)).mpr
    (by norm_num; exact hlow)

theorem mordellGaussian_quadratic (a : ℂ) (t : ℝ) :
    mordellGaussian a t =
      exp ((-2 * Real.pi : ℂ) * (t : ℂ) ^ 2 +
        (Real.pi * I * (1 + 2 * a) * (1 + I)) * t +
        Real.pi * I * (1 / 4 + a)) := by
  unfold mordellGaussian mordellLine
  congr 1
  ring_nf
  simp only [I_sq, I_pow_three]
  ring

theorem mordellGaussian_integrable (a : ℂ) : Integrable (mordellGaussian a) := by
  have hb : (-2 * (Real.pi : ℂ)).re < 0 := by
    norm_num
    nlinarith [Real.pi_pos]
  change Integrable (fun t : ℝ => mordellGaussian a t)
  simp_rw [mordellGaussian_quadratic]
  exact
    integrable_cexp_quadratic' hb (Real.pi * I * (1 + 2 * a) * (1 + I))
      (Real.pi * I * (1 / 4 + a))

theorem mordellKernel_integrable (a : ℂ) : Integrable (mordellKernel a) := by
  obtain ⟨C, _, hC⟩ := mordellDenominator_inv_bounded
  have h := (mordellGaussian_integrable a).mul_bdd
    mordellDenominator_inv_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)
  change Integrable (fun t : ℝ => mordellKernel a t)
  simpa only [mordellKernel, div_eq_mul_inv] using h.mul_const (1 + I)

theorem mordellKernel_difference (a : ℂ) (t : ℝ) :
    mordellKernel (a + 1) t - mordellKernel a t = mordellGaussian a t * (1 + I) := by
  have he : mordellGaussian (a + 1) t =
      mordellGaussian a t * exp (2 * Real.pi * I * mordellLine t) := by
    unfold mordellGaussian
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold mordellKernel
  rw [he]
  have hd := mordellDenominator_ne_zero t
  unfold mordellDenominator at hd ⊢
  field_simp

theorem mordellGaussian_integral (a : ℂ) :
    (∫ t : ℝ, mordellGaussian a t) =
      (1 / 2 : ℂ) ^ (1 / 2 : ℂ) * exp (-Real.pi * I * a ^ 2) := by
  have hb : (-2 * (Real.pi : ℂ)).re < 0 := by
    norm_num
    nlinarith [Real.pi_pos]
  simp_rw [mordellGaussian_quadratic]
  rw [integral_cexp_quadratic hb]
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2
  · field_simp
  · field_simp
    ring_nf
    simp only [I_sq, I_pow_three]
    ring

theorem mordellIntegral_difference (a : ℂ) :
    mordellIntegral (a + 1) - mordellIntegral a =
      ((1 / 2 : ℂ) ^ (1 / 2 : ℂ) * exp (-Real.pi * I * a ^ 2)) * (1 + I) := by
  rw [mordellIntegral, mordellIntegral, ← integral_sub (mordellKernel_integrable (a + 1))
    (mordellKernel_integrable a)]
  simp_rw [mordellKernel_difference]
  rw [integral_mul_const, mordellGaussian_integral]

end LiuWang.Proof.Campaign20260915.ZetaMordell
