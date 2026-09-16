import LiuWang.Proof.Campaign20260915.RosserCount.BacklundRightCircle
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundStripFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) *
    Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2))

-- Backlund (57), not the Riemann--Siegel Phi kernel.
def backlundStripPhi (s : ℂ) : ℂ :=
  backlundStripFactor s * riemannZeta s / Complex.log (-s * I)

theorem backlund_sine_mem_slitPlane {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 0 < s.im) :
    Complex.sin ((Real.pi : ℂ) * s / 2) ∈ Complex.slitPlane := by
  have hre : ((Real.pi : ℂ) * s / 2).re = Real.pi * s.re / 2 := by simp
  have him : ((Real.pi : ℂ) * s / 2).im = Real.pi * s.im / 2 := by simp
  have hreal : (Complex.sin ((Real.pi : ℂ) * s / 2)).re =
      Real.sin (Real.pi * s.re / 2) * Real.cosh (Real.pi * s.im / 2) := by
    rw [Complex.sin_eq, hre, him]
    norm_num only [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh,
      add_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero, zero_add]
  have himag : (Complex.sin ((Real.pi : ℂ) * s / 2)).im =
      Real.cos (Real.pi * s.re / 2) * Real.sinh (Real.pi * s.im / 2) := by
    rw [Complex.sin_eq, hre, him]
    norm_num only [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh,
      add_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero, zero_add, mul_one]
  rcases hs.eq_or_lt with hz | hp
  · apply Or.inr
    rw [himag, ← hz]
    simpa using (Real.sinh_pos_iff.mpr (by positivity : 0 < Real.pi * s.im / 2)).ne'
  · apply Or.inl
    rw [hreal]
    exact mul_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith [Real.pi_pos])) (Real.cosh_pos _)

theorem backlund_log_base_ne_zero {s : ℂ} (ht : 1 < s.im) :
    Complex.log (-s * I) ≠ 0 := by
  apply ne_zero_of_re_pos
  rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one]
  exact Real.log_pos (ht.trans_le (im_le_norm s))

theorem backlundStripPhi_differentiableAt {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1 < s.im) :
    DifferentiableAt ℂ backlundStripPhi s := by
  have hγ : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n he
    have h := congrArg Complex.im he
    simp only [div_ofNat_im, neg_im, natCast_im, neg_zero] at h
    linarith
  have hz : s ≠ 1 := by
    intro he
    have h := congrArg Complex.im he
    rw [one_im] at h
    linarith
  have hlog : -s * I ∈ Complex.slitPlane := by
    apply Or.inl
    simpa using (lt_trans zero_lt_one ht)
  have hp : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hpi)
  have hg := (differentiableAt_Gamma _ hγ).comp s
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z / 2) s)
  have hroot := (Complex.differentiableAt_sqrt
    (backlund_sine_mem_slitPlane hs hs' (by linarith))).comp s
      ((Complex.differentiable_sin.differentiableAt).comp s
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s))
  have hl := (Complex.differentiableAt_log hlog).comp s
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z * I) s)
  exact (((hp.mul hg).mul hroot).mul (differentiableAt_riemannZeta hz)).div hl
    (backlund_log_base_ne_zero ht)

theorem backlundStripFactor_norm_sq (s : ℂ) :
    ‖backlundStripFactor s‖ ^ 2 =
      Real.pi ^ (-s.re) * ‖Gamma (s / 2)‖ ^ 2 *
        ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ := by
  have hsqrt (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
    rw [Complex.sqrt, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg z)]
  have hp : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ^ 2 = Real.pi ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp only [div_ofNat_re, neg_re]
    rw [← Real.rpow_mul_natCast Real.pi_pos.le]
    congr 1
    ring
  rw [backlundStripFactor, norm_mul, norm_mul, mul_pow, mul_pow, hp, hsqrt]

theorem backlundStripFactor_norm_one {s : ℂ} (hs : s.re = 1) (ht : 0 < s.im) :
    ‖backlundStripFactor s‖ = 1 := by
  have hn : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 :=
    slitPlane_ne_zero (backlund_sine_mem_slitPlane (by rw [hs]; norm_num) hs.le ht)
  have hconj : 1 - s / 2 = conj (s / 2) := by
    apply Complex.ext
    · rw [conj_re]
      norm_num [hs]
    · rw [conj_im]
      simp
  have h := congrArg norm (Gamma_mul_Gamma_one_sub (s / 2))
  rw [hconj, Gamma_conj] at h
  simp only [norm_mul, norm_conj, norm_div, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at h
  rw [show (Real.pi : ℂ) * (s / 2) = (Real.pi : ℂ) * s / 2 by ring] at h
  have hγ : ‖Gamma (s / 2)‖ ^ 2 *
      ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ = Real.pi := by
    have hh := (eq_div_iff (norm_ne_zero_iff.mpr hn)).mp h
    nlinarith only [hh]
  have he : ‖backlundStripFactor s‖ ^ 2 = 1 := by
    rw [backlundStripFactor_norm_sq, hs, Real.rpow_neg_one, mul_assoc, hγ]
    exact inv_mul_cancel₀ Real.pi_ne_zero
  nlinarith [norm_nonneg (backlundStripFactor s)]

theorem backlundStripPhi_right_lt_one {s : ℂ} (hs : s.re = 1)
    (ht : 1000 ≤ s.im) :
    ‖backlundStripPhi s‖ < 1 := by
  have ht0 : 0 < s.im := by linarith
  have hz := backlund_zeta_right_growth (s := s) hs.ge (by rw [hs]; norm_num)
    (by rwa [abs_of_pos ht0])
  rw [abs_of_pos ht0] at hz
  have hl : Real.log s.im ≤ ‖Complex.log (-s * I)‖ := by
    calc
      _ ≤ Real.log ‖s‖ := Real.log_le_log ht0 (im_le_norm s)
      _ = (Complex.log (-s * I)).re := by
        rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one]
      _ ≤ _ := re_le_norm _
  rw [backlundStripPhi, norm_div, norm_mul, backlundStripFactor_norm_one hs ht0, one_mul]
  apply (div_lt_one (norm_pos_iff.mpr (backlund_log_base_ne_zero (by linarith)))).mpr
  linarith

#print axioms backlund_sine_mem_slitPlane
#print axioms backlund_log_base_ne_zero
#print axioms backlundStripPhi_differentiableAt
#print axioms backlundStripFactor_norm_sq
#print axioms backlundStripFactor_norm_one
#print axioms backlundStripPhi_right_lt_one

end LiuWang.Proof.Campaign20260915.RosserCount
