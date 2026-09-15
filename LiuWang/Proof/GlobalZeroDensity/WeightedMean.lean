import LiuWang.Proof.GlobalZeroDensity.CriticalLine
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
The full-line weighted critical mean is absolutely integrable. An explicit
coarse bound is proved from the actual detector, not postulated as mean data.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.GlobalZeroDensity

def weightedMean (y σ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2

theorem norm_cos_ge_exp (z : ℂ) (hz : |z.re| ≤ 1) :
    Real.exp |z.im| / 4 ≤ ‖Complex.cos z‖ := by
  have hcos : 1 / 2 ≤ Real.cos z.re := by
    have hs : z.re ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        pow_le_pow_left₀ (abs_nonneg z.re) hz 2
    have h := Real.one_sub_sq_div_two_le_cos (x := z.re)
    linarith
  have hcosh : Real.exp |z.im| / 2 ≤ Real.cosh z.im := by
    rw [Real.cosh_eq]
    rcases le_total 0 z.im with hi | hi
    · rw [abs_of_nonneg hi]
      linarith [Real.exp_pos (-z.im)]
    · rw [abs_of_nonpos hi]
      linarith [Real.exp_pos z.im]
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp [Complex.cos_ofReal_re]
  have h := mul_le_mul hcos hcosh (by positivity) (by linarith : 0 ≤ Real.cos z.re)
  have hnorm := Complex.re_le_norm (Complex.cos z)
  rw [hre] at hnorm
  linarith

theorem norm_regularG_critical_le {y : ℝ} (hy : 1 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      4 * ‖f y ((1 / 2 : ℂ) + t * Complex.I)‖ *
        Real.exp (- |t| / (2 * y)) := by
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  have hy0 : 0 < y := by linarith
  have hs : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hnorm : ‖s - 1‖ = ‖s‖ := by
    have h1 := Complex.sq_norm (s - 1)
    have h2 := Complex.sq_norm s
    simp [Complex.normSq_apply, s] at h1 h2
    nlinarith [norm_nonneg (s - 1), norm_nonneg s]
  have hre : |(s / (2 * (y : ℂ))).re| ≤ 1 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
    linarith
  have hi : |(s / (2 * (y : ℂ))).im| = |t| / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp [s, abs_div, abs_of_pos hy0, abs_mul]
  have hcos := norm_cos_ge_exp (s / (2 * (y : ℂ))) hre
  rw [hi] at hcos
  have hcpos : 0 < ‖Complex.cos (s / (2 * (y : ℂ)))‖ :=
    (by positivity : 0 < Real.exp (|t| / (2 * y)) / 4).trans_le hcos
  change ‖regularG y s‖ ≤ _
  rw [regularG_eq_g hs, g, norm_mul, norm_div, norm_mul, hnorm]
  have hspos := norm_pos_iff.mpr hs0
  rw [div_mul_eq_div_div, div_self hspos.ne', one_div]
  have hinv : ‖Complex.cos (s / (2 * (y : ℂ)))‖⁻¹ ≤
      4 * Real.exp (- |t| / (2 * y)) := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < Real.exp (|t| / (2 * y)) / 4) hcos
    rw [← one_div]
    calc
      _ ≤ 1 / (Real.exp (|t| / (2 * y)) / 4) := h
      _ = 4 * Real.exp (- |t| / (2 * y)) := by
        rw [neg_div, Real.exp_neg]
        field_simp
  nlinarith [mul_le_mul_of_nonneg_right hinv (norm_nonneg (f y s))]

theorem F_critical_quadratic_le (y t : ℝ) :
    F y ((1 / 2 : ℂ) + t * Complex.I) ≤
      (256 * (⌈y⌉₊ : ℝ) + 2) + 64 * (⌈y⌉₊ : ℝ) * t ^ 2 := by
  have h := F_critical_le y t
  have hs := Real.sq_sqrt (Nat.cast_nonneg ⌈y⌉₊ : (0 : ℝ) ≤ ⌈y⌉₊)
  have ha := sq_nonneg ((8 + 4 * |t|) * Real.sqrt ⌈y⌉₊ - 1)
  have hb := sq_nonneg (8 - 4 * |t|)
  have hc := mul_nonneg (Nat.cast_nonneg ⌈y⌉₊ : (0 : ℝ) ≤ ⌈y⌉₊) hb
  nlinarith [sq_abs t]

theorem regularG_critical_sq_le {y : ℝ} (hy : 1 ≤ y) (t : ℝ) :
    ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      ((4096 * (⌈y⌉₊ : ℝ) + 32) + 1024 * (⌈y⌉₊ : ℝ) * |t| ^ 2) *
        Real.exp (- |t| / y) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_regularG_critical_le hy t) 2
  have he : Real.exp (- |t| / (2 * y)) ^ 2 = Real.exp (- |t| / y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, mul_pow, he] at h
  have hf := mul_le_mul_of_nonneg_right (F_critical_quadratic_le y t)
    (Real.exp_pos (- |t| / y)).le
  simp only [F] at hf
  rw [sq_abs]
  nlinarith

theorem exp_moment_integrable {y : ℝ} (hy : 0 < y) (j : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-t / y)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (j : ℝ)) (p := 1) (b := y⁻¹)
    (by have := Nat.cast_nonneg (α := ℝ) j; linarith) (by norm_num) (by positivity)
  simpa only [Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv, neg_mul, mul_neg,
    mul_comm, mul_one] using h

theorem exp_moment_integral {y : ℝ} (hy : 0 < y) (j : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ j * Real.exp (-t / y)) =
      y ^ (j + 1) * (Nat.factorial j : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (j : ℝ) + 1) (r := y⁻¹) (by positivity) (by positivity)
  rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by simp,
    Real.rpow_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial, one_div, inv_inv, div_eq_mul_inv, neg_mul, mul_neg,
    mul_comm, mul_one] using h

theorem integrable_abs_of_integrableOn {v : ℝ → ℝ} (hv : IntegrableOn v (Ioi 0)) :
    Integrable (fun t : ℝ => v |t|) := by
  have hp : IntegrableOn (fun t : ℝ => v |t|) (Ioi 0) :=
    hv.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hn : IntegrableOn (fun t : ℝ => v |t|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

theorem critical_envelope_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ =>
      ((4096 * (⌈y⌉₊ : ℝ) + 32) + 1024 * (⌈y⌉₊ : ℝ) * |t| ^ 2) *
        Real.exp (- |t| / y)) := by
  apply integrable_abs_of_integrableOn (v := fun t : ℝ =>
    ((4096 * (⌈y⌉₊ : ℝ) + 32) + 1024 * (⌈y⌉₊ : ℝ) * t ^ 2) *
      Real.exp (-t / y))
  have h0 := (exp_moment_integrable hy 0).const_mul (4096 * (⌈y⌉₊ : ℝ) + 32)
  have h2 := (exp_moment_integrable hy 2).const_mul (1024 * (⌈y⌉₊ : ℝ))
  unfold IntegrableOn
  simpa only [pow_zero, one_mul, add_mul, mul_assoc] using h0.fun_add h2

theorem integrable_regularG_critical_sq {y : ℝ} (hy : 1 ≤ y) :
    Integrable (fun t : ℝ => ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hpi : 1 / 2 < Real.pi * y := by
    nlinarith [Real.pi_gt_three]
  have hc := continuous_vertical_regularG hy0 (by norm_num : (0 : ℝ) < 1 / 2) hpi
  apply (critical_envelope_integrable hy0).mono' _
    (Filter.Eventually.of_forall (fun t => ?_))
  · have hc' : Continuous (fun t : ℝ =>
        ‖regularG y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) := by
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Pi.pow_apply]
        using hc.norm.fun_pow 2
    exact hc'.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact regularG_critical_sq_le hy t

theorem weightedMean_critical_le {y : ℝ} (hy : 1 ≤ y) :
    weightedMean y (1 / 2) ≤
      (8192 * (⌈y⌉₊ : ℝ) + 64) * y + 4096 * (⌈y⌉₊ : ℝ) * y ^ 3 := by
  have hy0 : 0 < y := by linarith
  have h := integral_mono (integrable_regularG_critical_sq hy)
    (critical_envelope_integrable hy0) (regularG_critical_sq_le hy)
  rw [integral_comp_abs (f := fun t : ℝ =>
    ((4096 * (⌈y⌉₊ : ℝ) + 32) + 1024 * (⌈y⌉₊ : ℝ) * t ^ 2) *
      Real.exp (-t / y))] at h
  have h0 := (exp_moment_integrable hy0 0).const_mul (4096 * (⌈y⌉₊ : ℝ) + 32)
  have h2 := (exp_moment_integrable hy0 2).const_mul (1024 * (⌈y⌉₊ : ℝ))
  simp only [pow_zero, one_mul] at h0
  have hfun : (fun t : ℝ =>
      ((4096 * (⌈y⌉₊ : ℝ) + 32) + 1024 * (⌈y⌉₊ : ℝ) * t ^ 2) *
        Real.exp (-t / y)) =
      (fun t : ℝ => (4096 * (⌈y⌉₊ : ℝ) + 32) * Real.exp (-t / y) +
        (1024 * (⌈y⌉₊ : ℝ)) * (t ^ 2 * Real.exp (-t / y))) := by
    funext t
    ring
  rw [hfun] at h
  rw [integral_add h0 h2, integral_const_mul, integral_const_mul] at h
  have he0 := exp_moment_integral hy0 0
  simp only [pow_zero, one_mul, zero_add, pow_one, Nat.factorial_zero, Nat.cast_one,
    mul_one] at he0
  rw [he0, exp_moment_integral hy0 2] at h
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one] at h
  simp only [weightedMean, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  convert h using 1
  · rfl
  · ring

end LiuWang.Proof.GlobalZeroDensity
