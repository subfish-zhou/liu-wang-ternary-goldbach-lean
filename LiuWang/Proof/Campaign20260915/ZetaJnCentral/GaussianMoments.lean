import LiuWang.Proof.Campaign20260915.ZetaJnCentral.FirstOrderIntegral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

def gaussianMomentEnvelope (N : ℕ) : ℝ :=
  3 * (((N + 1).factorial : ℝ) + (N.factorial : ℝ) / (Real.sqrt 2 * Real.pi))

def gaussianMomentBudget (N : ℕ) : ℝ := gaussianMomentEnvelope N * Real.sqrt 2

theorem gaussianMomentEnvelope_nonneg (N : ℕ) : 0 ≤ gaussianMomentEnvelope N := by
  unfold gaussianMomentEnvelope
  positivity

theorem gaussianMoment_pointwise (N : ℕ) (y : ℝ) :
    Real.exp (-Real.pi * y ^ 2) * |y| ^ N * (|y| + 1 / (Real.sqrt 2 * Real.pi)) ≤
      gaussianMomentEnvelope N * Real.exp (-Real.pi / 2 * y ^ 2) := by
  have h1 := exterior_power_gaussian (N + 1) y
  have h0 := mul_le_mul_of_nonneg_right (exterior_power_gaussian N y)
    (by positivity : 0 ≤ 1 / (Real.sqrt 2 * Real.pi))
  rw [pow_succ] at h1
  unfold gaussianMomentEnvelope
  linear_combination h1 + h0

theorem norm_interval_of_gaussian {f : ℝ → ℂ} {a b B : ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B)
    (hb : ∀ y ∈ Icc a b, ‖f y‖ ≤ B * Real.exp (-Real.pi / 2 * y ^ 2)) :
    ‖∫ y : ℝ in a..b, f y‖ ≤ B * Real.sqrt 2 := by
  have hi : IntervalIntegrable (fun y : ℝ => B * Real.exp (-Real.pi / 2 * y ^ 2)) volume a b :=
    (by fun_prop : Continuous (fun y : ℝ => B * Real.exp (-Real.pi / 2 * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in a..b, B * Real.exp (-Real.pi / 2 * y ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le hab
        (Filter.Eventually.of_forall (fun y hy => hb y ⟨hy.1.le, hy.2⟩)) hi
    _ = B * (∫ y : ℝ in a..b, Real.exp (-Real.pi / 2 * y ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ B * Real.sqrt (Real.pi / (Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [neg_div] using gaussian_interval_le_full
          (by positivity : 0 < Real.pi / 2) hab) hB
    _ = _ := by rw [show Real.pi / (Real.pi / 2) = 2 by field_simp]

theorem jn_central_gaussian_integral (sigma : ℝ) {eta R d : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 ≤ d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (-d)..d, rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      centralTaylorConstant sigma eta R (N + 1) * gaussianMomentBudget N := by
  have hC := centralTaylorConstant_nonneg sigma eta hR0 (N + 1)
  have hb (y : ℝ) (hy : y ∈ Icc (-d) d) :
      ‖rsJnIntegrand sigma eta m (N + 1) y‖ ≤
        (centralTaylorConstant sigma eta R (N + 1) * gaussianMomentEnvelope N) *
          Real.exp (-Real.pi / 2 * y ^ 2) := by
    have hyd : |y| ≤ d := abs_le.mpr hy
    have h := jn_central_pointwise sigma he hR0 hR (y := y)
      (by nlinarith [mul_le_mul_of_nonneg_left hyd rsSaddleScale_pos.le]) hm0 hm1 N
    apply h.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussianMoment_pointwise N y) hC
  exact (norm_interval_of_gaussian (by linarith)
    (mul_nonneg hC (gaussianMomentEnvelope_nonneg N)) hb).trans_eq (by
      unfold gaussianMomentBudget
      ring)

def gaussianMonomial (eta : ℝ) (m N : ℕ) (y : ℝ) : ℂ :=
  rsDescentDirection * rsGaussianKernel eta m (rsDescentPoint eta y) *
    (rsDescentPoint eta y - eta) ^ (N + 1)

theorem gaussianMonomial_pointwise (eta : ℝ) (m N : ℕ)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (y : ℝ) :
    ‖gaussianMonomial eta m N y‖ ≤
      gaussianMomentEnvelope N * Real.exp (-Real.pi / 2 * y ^ 2) := by
  by_cases hy : y = 0
  · subst y
    simp only [gaussianMonomial, rsDescentPoint, ofReal_zero, mul_zero, add_zero,
      sub_self, zero_pow (Nat.succ_ne_zero N), mul_zero, norm_zero]
    exact mul_nonneg (gaussianMomentEnvelope_nonneg N) (Real.exp_pos _).le
  rw [gaussianMonomial, norm_mul, norm_mul, rsDescentDirection_norm, one_mul,
    norm_pow, rsDescentPoint_distance, pow_succ]
  have h := mul_le_mul_of_nonneg_right (gaussian_times_distance eta m hy hm0 hm1)
    (pow_nonneg (abs_nonneg y) N)
  have h' : ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ * (|y| ^ N * |y|) ≤
      Real.exp (-Real.pi * y ^ 2) * |y| ^ N * (|y| + 1 / (Real.sqrt 2 * Real.pi)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  exact h'.trans (gaussianMoment_pointwise N y)

theorem gaussianMonomial_integrable (eta : ℝ) (m N : ℕ)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    Integrable (gaussianMonomial eta m N) := by
  have hm : Measurable (gaussianMonomial eta m N) := by
    unfold gaussianMonomial rsGaussianKernel rsHankelDenominator rsDescentPoint
    fun_prop
  apply ((integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul
    (gaussianMomentEnvelope N)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [neg_div] using gaussianMonomial_pointwise eta m N hm0 hm1 y)

theorem gaussianMonomial_interval (eta : ℝ) (m N : ℕ)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ y : ℝ in a..b, gaussianMonomial eta m N y‖ ≤ gaussianMomentBudget N := by
  exact norm_interval_of_gaussian hab (gaussianMomentEnvelope_nonneg N)
    (fun y _ => gaussianMonomial_pointwise eta m N hm0 hm1 y)

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
