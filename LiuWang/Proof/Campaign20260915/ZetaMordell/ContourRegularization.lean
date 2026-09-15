import LiuWang.Proof.Campaign20260915.ZetaMordell.DirectedIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open scoped Real Topology

namespace LiuWang.Proof.Campaign20260915.ZetaMordell

def mordellRotor : ℂ := (1 + I) / 4

def mordellRotatedKernel (a w : ℂ) : ℂ :=
  mordellRotor *
    exp (Real.pi * I * (mordellRotor * w) ^ 2 +
      2 * Real.pi * I * a * (mordellRotor * w)) /
    (exp (2 * Real.pi * I * mordellRotor * w) - 1)

def mordellAmplitude (a w : ℂ) : ℂ :=
  exp (Real.pi * I * (mordellRotor * w) ^ 2 +
    2 * Real.pi * I * a * (mordellRotor * w)) /
      dslope exp 0 (2 * Real.pi * I * mordellRotor * w)

def mordellRegularKernel (a w : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * dslope (mordellAmplitude a) 0 w

theorem mordellRotor_ne_zero : mordellRotor ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [mordellRotor] at this

theorem mordellFrequency_ne_zero : (2 * Real.pi * I : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

theorem mordellRotated_exp_eq_one {w : ℂ} (hw : |w.im| ≤ 1) :
    exp (2 * Real.pi * I * mordellRotor * w) = 1 ↔ w = 0 := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    have hx : mordellRotor * w = (n : ℂ) := by
      apply mul_left_cancel₀ mordellFrequency_ne_zero
      convert hn using 1 <;> ring
    have hw' : w = (n : ℂ) * (2 - 2 * I) := by
      apply mul_left_cancel₀ mordellRotor_ne_zero
      rw [hx]
      unfold mordellRotor
      ring_nf
      simp only [I_sq]
      ring
    have hi := congrArg Complex.im hw'
    norm_num [mul_im, mul_re] at hi
    have hn' : (-1 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := by
      have h := abs_le.mp hw
      constructor <;> linarith
    have hn'' : (-1 : ℤ) < n ∧ n < 1 := by exact_mod_cast hn'
    have hn0 : n = 0 := by omega
    simpa [hn0] using hw'
  · rintro rfl
    simp

theorem mordellExpSlope_ne_zero {w : ℂ} (hw : |w.im| ≤ 1) :
    dslope exp 0 (2 * Real.pi * I * mordellRotor * w) ≠ 0 := by
  intro h
  have he := sub_smul_dslope exp 0 (2 * Real.pi * I * mordellRotor * w)
  simp only [h, smul_zero, exp_zero] at he
  have hw0 := (mordellRotated_exp_eq_one hw).mp (sub_eq_zero.mp he.symm)
  subst w
  simp [dslope_same, Complex.deriv_exp] at h

theorem analyticAt_dslope_zero {f : ℂ → ℂ} (h0 : AnalyticAt ℂ f 0)
    {w : ℂ} (hw : AnalyticAt ℂ f w) : AnalyticAt ℂ (dslope f 0) w := by
  by_cases he : w = 0
  · subst w
    obtain ⟨p, hp⟩ := h0
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hg : dslope f 0 =ᶠ[𝓝 w] fun z => (f z - f 0) / z := by
      filter_upwards [dslope_eventuallyEq_slope_of_ne f he] with z hz
      simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using hz
    exact ((hw.sub analyticAt_const).div analyticAt_id he).congr hg.symm

theorem mordellAmplitude_analytic (a : ℂ) {w : ℂ} (hw : |w.im| ≤ 1) :
    AnalyticAt ℂ (mordellAmplitude a) w := by
  have hn : AnalyticAt ℂ (fun z : ℂ =>
      exp (Real.pi * I * (mordellRotor * z) ^ 2 +
        2 * Real.pi * I * a * (mordellRotor * z))) w := by
    apply AnalyticAt.cexp
    fun_prop
  have hd : AnalyticAt ℂ (fun z : ℂ =>
      dslope exp 0 (2 * Real.pi * I * mordellRotor * z)) w :=
    (analyticAt_dslope_zero analyticAt_id.cexp analyticAt_id.cexp).comp (by fun_prop)
  exact hn.div hd (mordellExpSlope_ne_zero hw)

theorem mordellAmplitude_zero (a : ℂ) : mordellAmplitude a 0 = 1 := by
  simp [mordellAmplitude, dslope_same, Complex.deriv_exp]

theorem mordellRegularKernel_analytic (a : ℂ) {w : ℂ} (hw : |w.im| ≤ 1) :
    AnalyticAt ℂ (mordellRegularKernel a) w :=
  analyticAt_const.mul (analyticAt_dslope_zero
    (mordellAmplitude_analytic a (by simp)) (mordellAmplitude_analytic a hw))

theorem mordellRegularKernel_eq (a : ℂ) {w : ℂ} (hw : |w.im| ≤ 1) (h0 : w ≠ 0) :
    mordellRegularKernel a w =
      mordellRotatedKernel a w - (2 * Real.pi * I : ℂ)⁻¹ / w := by
  have hf := mordellFrequency_ne_zero
  have hr := mordellRotor_ne_zero
  have he := mordellExpSlope_ne_zero hw
  have hd := sub_smul_dslope exp 0 (2 * Real.pi * I * mordellRotor * w)
  simp only [sub_zero, smul_eq_mul, exp_zero] at hd
  have hd0 : exp (2 * Real.pi * I * mordellRotor * w) - 1 ≠ 0 := by
    rw [← hd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hf hr) h0) he
  simp only [mordellRegularKernel, dslope_of_ne _ h0, slope, sub_zero, smul_eq_mul,
    vsub_eq_sub, mordellAmplitude_zero, mordellRotatedKernel]
  unfold mordellAmplitude
  rw [← hd]
  field_simp

theorem mordellPole_horizontal_difference (t : ℝ) :
    (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) - I) -
      (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) + I) =
        ((Real.pi : ℂ)⁻¹) * (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hm : (t : ℂ) - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hp : (t : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have ht : (1 + (t : ℂ) ^ 2) ≠ 0 := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  simp only [I_pow_three]
  ring

theorem mordellPole_difference_integrable :
    Integrable (fun t : ℝ => (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) - I) -
      (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) + I)) := by
  simp_rw [mordellPole_horizontal_difference]
  exact (integrable_inv_one_add_sq.ofReal).const_mul _

theorem mordellPole_difference_integral :
    (∫ t : ℝ, (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) - I) -
      (2 * Real.pi * I : ℂ)⁻¹ / ((t : ℂ) + I)) = 1 := by
  simp_rw [mordellPole_horizontal_difference]
  rw [integral_const_mul]
  rw [integral_complex_ofReal, integral_univ_inv_one_add_sq]
  exact inv_mul_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)

end LiuWang.Proof.Campaign20260915.ZetaMordell
