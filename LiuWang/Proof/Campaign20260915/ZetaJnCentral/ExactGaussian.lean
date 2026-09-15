import LiuWang.Proof.Campaign20260915.ZetaJnCentral.GaussianMoments

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def gaussianAbsoluteMoment (b : ℝ) (n : ℕ) : ℝ :=
  (1 / b) ^ (((n : ℝ) + 1) / 2) * Real.Gamma (((n : ℝ) + 1) / 2)

theorem absoluteGaussian_integrable {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun y : ℝ => |y| ^ n * Real.exp (-b * y ^ 2)) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb
    (show (-1 : ℝ) < (n : ℝ) by have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp] using h

theorem absoluteGaussian_integral {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (∫ y : ℝ, |y| ^ n * Real.exp (-b * y ^ 2)) = gaussianAbsoluteMoment b n := by
  have hs := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show 0 < ((n : ℝ) + 1) / 2 by positivity) hb
  rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  have hp : (∫ y : ℝ in Ioi 0, (2 * y ^ ((2 : ℝ) - 1)) *
      ((y ^ (2 : ℝ)) ^ (((n : ℝ) + 1) / 2 - 1) *
        Real.exp (-(b * y ^ (2 : ℝ))))) =
      2 * ∫ y : ℝ in Ioi 0, y ^ n * Real.exp (-b * y ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    have hpow : y * (y ^ (2 : ℝ)) ^ (((n : ℝ) + 1) / 2 - 1) = y ^ n := by
      rw [← Real.rpow_mul hy0.le]
      nth_rw 1 [← Real.rpow_one y]
      rw [← Real.rpow_add hy0]
      convert Real.rpow_natCast y n using 2
      ring
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [show 2 * y * ((y ^ (2 : ℝ)) ^ (((n : ℝ) + 1) / 2 - 1) *
        Real.exp (-(b * y ^ (2 : ℝ)))) =
      2 * (y * (y ^ (2 : ℝ)) ^ (((n : ℝ) + 1) / 2 - 1)) *
        Real.exp (-(b * y ^ (2 : ℝ))) by ring, hpow]
    simp only [Real.rpow_two, neg_mul, mul_assoc]
  simp only [smul_eq_mul] at hs
  rw [hp] at hs
  have habs := integral_comp_abs (f := fun y : ℝ => y ^ n * Real.exp (-b * y ^ 2))
  simpa only [sq_abs, gaussianAbsoluteMoment] using habs.trans hs

theorem gaussianAbsoluteMoment_nonneg {b : ℝ} (hb : 0 < b) (n : ℕ) :
    0 ≤ gaussianAbsoluteMoment b n := by
  rw [← absoluteGaussian_integral hb n]
  exact integral_nonneg (fun y => by positivity)

theorem gaussianAbsoluteMoment_zero {b : ℝ} (hb : 0 < b) :
    gaussianAbsoluteMoment b 0 = Real.sqrt (Real.pi / b) := by
  rw [← absoluteGaussian_integral hb]
  simpa only [pow_zero, one_mul] using integral_gaussian b

theorem gaussianAbsoluteMoment_one {b : ℝ} :
    gaussianAbsoluteMoment b 1 = 1 / b := by
  norm_num [gaussianAbsoluteMoment]

theorem gaussianAbsoluteMoment_step {b : ℝ} (hb : 0 < b) (n : ℕ) :
    gaussianAbsoluteMoment b (n + 2) =
      ((n : ℝ) + 1) / (2 * b) * gaussianAbsoluteMoment b n := by
  unfold gaussianAbsoluteMoment
  have he : (((n + 2 : ℕ) : ℝ) + 1) / 2 = ((n : ℝ) + 1) / 2 + 1 := by
    push_cast
    ring
  rw [he, Real.rpow_add (by positivity), Real.rpow_one,
    Real.Gamma_add_one (by positivity : ((n : ℝ) + 1) / 2 ≠ 0)]
  ring

def exactGaussianWeight (b : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.exp (-b * y ^ 2) * |y| ^ n * (|y| + 1 / (Real.sqrt 2 * Real.pi))

def exactGaussianBudget (b : ℝ) (n : ℕ) : ℝ :=
  gaussianAbsoluteMoment b (n + 1) + gaussianAbsoluteMoment b n / (Real.sqrt 2 * Real.pi)

theorem exactGaussianWeight_expand (b : ℝ) (n : ℕ) (y : ℝ) :
    exactGaussianWeight b n y = |y| ^ (n + 1) * Real.exp (-b * y ^ 2) +
      (|y| ^ n * Real.exp (-b * y ^ 2)) / (Real.sqrt 2 * Real.pi) := by
  unfold exactGaussianWeight
  rw [pow_succ]
  ring

theorem exactGaussianWeight_integrable {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (exactGaussianWeight b n) := by
  change Integrable (fun y => exactGaussianWeight b n y)
  simp_rw [exactGaussianWeight_expand]
  exact (absoluteGaussian_integrable hb (n + 1)).add
    ((absoluteGaussian_integrable hb n).div_const (Real.sqrt 2 * Real.pi))

theorem exactGaussianWeight_integral {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (∫ y : ℝ, exactGaussianWeight b n y) = exactGaussianBudget b n := by
  have he : exactGaussianWeight b n = fun y : ℝ =>
      |y| ^ (n + 1) * Real.exp (-b * y ^ 2) +
        (|y| ^ n * Real.exp (-b * y ^ 2)) / (Real.sqrt 2 * Real.pi) := by
    funext y
    exact exactGaussianWeight_expand b n y
  rw [he, integral_add (absoluteGaussian_integrable hb (n + 1))
    ((absoluteGaussian_integrable hb n).div_const _), integral_div,
    absoluteGaussian_integral hb, absoluteGaussian_integral hb]
  rfl

theorem norm_interval_exactGaussian {f : ℝ → ℂ} {b a d C : ℝ} (n : ℕ)
    (hb : 0 < b) (had : a ≤ d) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc a d, ‖f y‖ ≤ C * exactGaussianWeight b n y) :
    ‖∫ y : ℝ in a..d, f y‖ ≤ C * exactGaussianBudget b n := by
  have hi := (exactGaussianWeight_integrable hb n).const_mul C
  calc
    _ ≤ ∫ y : ℝ in a..d, C * exactGaussianWeight b n y :=
      intervalIntegral.norm_integral_le_of_norm_le had
        (Filter.Eventually.of_forall (fun y hy => hf y ⟨hy.1.le, hy.2⟩)) hi.intervalIntegrable
    _ ≤ ∫ y : ℝ, C * exactGaussianWeight b n y := by
      rw [intervalIntegral.integral_of_le had]
      exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun y =>
        mul_nonneg hC (by unfold exactGaussianWeight; positivity)))
    _ = _ := by rw [integral_const_mul, exactGaussianWeight_integral hb]

theorem jn_central_exact_integral (sigma : ℝ) {eta R d : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 ≤ d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (-d)..d, rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      centralTaylorConstant sigma eta R (N + 1) * exactGaussianBudget Real.pi N := by
  apply norm_interval_exactGaussian N Real.pi_pos (by linarith)
    (centralTaylorConstant_nonneg sigma eta hR0 _)
  intro y hy
  have hyd : |y| ≤ d := abs_le.mpr hy
  simpa only [exactGaussianWeight, mul_assoc] using
    jn_central_pointwise sigma he hR0 hR (y := y)
      ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyd rsSaddleScale_pos.le)
        (by norm_num : (0 : ℝ) ≤ 21 / 20)).trans hdR) hm0 hm1 N

theorem gaussianMonomial_exact_interval (eta : ℝ) (m N : ℕ)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ y : ℝ in a..b, gaussianMonomial eta m N y‖ ≤ exactGaussianBudget Real.pi N := by
  apply (norm_interval_exactGaussian N Real.pi_pos hab (show (0 : ℝ) ≤ 1 by norm_num) ?_).trans_eq
    (one_mul _)
  intro y _
  by_cases hy : y = 0
  · subst y
    simp only [gaussianMonomial, rsDescentPoint, ofReal_zero, mul_zero, add_zero,
      sub_self, zero_pow (Nat.succ_ne_zero N), mul_zero, norm_zero, one_mul]
    unfold exactGaussianWeight
    positivity
  rw [gaussianMonomial, norm_mul, norm_mul, rsDescentDirection_norm, one_mul,
    norm_pow, rsDescentPoint_distance, pow_succ]
  have h := mul_le_mul_of_nonneg_right (gaussian_times_distance eta m hy hm0 hm1)
    (pow_nonneg (abs_nonneg y) N)
  simpa only [exactGaussianWeight, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
