import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MiddleSegments

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem positive_div_one_sub_exp_neg {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    x / (1 - Real.exp (-c * x)) ≤ x + 1 / c := by
  have hp : 0 < 1 - Real.exp (-c * x) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c * x))
    (Real.exp_pos (-c * x)).le
  have hi : Real.exp (c * x) * Real.exp (-c * x) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  rw [hi] at he
  rw [div_le_iff₀ hp]
  have h := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hc.le)
  have hid : (c * x + 1) * Real.exp (-c * x) * c⁻¹ =
      (x + 1 / c) * Real.exp (-c * x) := by
    field_simp
  rw [hid, one_mul, ← one_div] at h
  nlinarith

theorem jn_zero (sigma eta : ℝ) (m N : ℕ) :
    rsJnIntegrand sigma eta m (N + 1) 0 = 0 := by
  have hsum :
      (∑ n ∈ Finset.range (N + 1), rsSaddleCoefficient sigma (rsSaddleScale * eta) n *
        (0 : ℂ) ^ n) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [rsSaddle_coefficient_zero]
    · intro b _ hb
      simp [zero_pow hb]
    · simp
  simp only [rsJnIntegrand, rsDescentPoint, ofReal_zero, mul_zero, add_zero,
    sub_self, rsSaddleRemainder, rsSaddle_zero, hsum]

theorem gaussian_times_distance (eta : ℝ) (m : ℕ) {y : ℝ}
    (hy : y ≠ 0) (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ * |y| ≤
      Real.exp (-Real.pi * y ^ 2) * (|y| + 1 / (Real.sqrt 2 * Real.pi)) := by
  have h := exterior_gaussian_bound eta m (abs_pos.mpr hy) le_rfl hm0 hm1
  calc
    _ ≤ (Real.exp (-Real.pi * y ^ 2) /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * |y|))) * |y| :=
      mul_le_mul_of_nonneg_right h (abs_nonneg y)
    _ = Real.exp (-Real.pi * y ^ 2) *
        (|y| / (1 - Real.exp (-(Real.sqrt 2 * Real.pi) * |y|))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (positive_div_one_sub_exp_neg (by positivity) (abs_pos.mpr hy)) (Real.exp_pos _).le

def centralTaylorConstant (sigma eta R : ℝ) (N : ℕ) : ℝ :=
  21 * rsSourceMajorant sigma (rsSaddleScale * eta) R * (rsSaddleScale / R) ^ N

theorem centralTaylorConstant_nonneg (sigma eta : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ) :
    0 ≤ centralTaylorConstant sigma eta R N := by
  unfold centralTaylorConstant rsSourceMajorant
  have := rsSaddleScale_pos
  positivity

theorem jn_central_pointwise (sigma : ℝ) {eta R y : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hyR : 21 / 20 * (rsSaddleScale * |y|) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      centralTaylorConstant sigma eta R (N + 1) * Real.exp (-Real.pi * y ^ 2) *
        |y| ^ N * (|y| + 1 / (Real.sqrt 2 * Real.pi)) := by
  by_cases hy : y = 0
  · subst y
    rw [jn_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (centralTaylorConstant_nonneg sigma eta hR0 _) (Real.exp_pos _).le)
      (pow_nonneg (abs_nonneg _) _)) (by positivity)
  have hz : ‖(rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)‖ =
      rsSaddleScale * |y| := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos rsSaddleScale_pos,
      rsDescentPoint_distance]
  have hr := rsSaddle_source_remainder_twenty_one sigma (mul_pos rsSaddleScale_pos he)
    hR0 hR (z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))
    (by rw [hz]; exact hyR) (N + 1)
  rw [hz] at hr
  change ‖rsSaddleRemainder sigma (rsSaddleScale * eta) (N + 1)
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))‖ ≤ _ at hr
  have hr' : ‖rsSaddleRemainder sigma (rsSaddleScale * eta) (N + 1)
      ((rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta))‖ ≤
      centralTaylorConstant sigma eta R (N + 1) * |y| ^ (N + 1) := by
    convert hr using 1
    unfold centralTaylorConstant
    rw [show rsSaddleScale * |y| / R = (rsSaddleScale / R) * |y| by ring, mul_pow]
    ring
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul]
  calc
    _ ≤ ‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ *
        (centralTaylorConstant sigma eta R (N + 1) * |y| ^ (N + 1)) :=
      mul_le_mul_of_nonneg_left hr' (norm_nonneg _)
    _ = (centralTaylorConstant sigma eta R (N + 1) * |y| ^ N) *
        (‖rsGaussianKernel eta m (rsDescentPoint eta y)‖ * |y|) := by
      rw [pow_succ]
      ring
    _ ≤ (centralTaylorConstant sigma eta R (N + 1) * |y| ^ N) *
        (Real.exp (-Real.pi * y ^ 2) * (|y| + 1 / (Real.sqrt 2 * Real.pi))) :=
      mul_le_mul_of_nonneg_left (gaussian_times_distance eta m hy hm0 hm1)
        (mul_nonneg (centralTaylorConstant_nonneg sigma eta hR0 _)
          (pow_nonneg (abs_nonneg _) _))
    _ = _ := by ring

def centralIntervalBudget (sigma eta R d : ℝ) (N : ℕ) : ℝ :=
  2 * d * (centralTaylorConstant sigma eta R (N + 1) *
    d ^ N * (d + 1 / (Real.sqrt 2 * Real.pi)))

theorem jn_central_integral (sigma : ℝ) {eta R d : ℝ} {m : ℕ}
    (he : 0 < eta) (hR0 : 0 < R) (hR : R ≤ 3 / 5 * (rsSaddleScale * eta))
    (hd : 0 ≤ d) (hdR : 21 / 20 * (rsSaddleScale * d) ≤ R)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) (N : ℕ) :
    ‖∫ y : ℝ in (-d)..d, rsJnIntegrand sigma eta m (N + 1) y‖ ≤
      centralIntervalBudget sigma eta R d N := by
  have hC := centralTaylorConstant_nonneg sigma eta hR0 (N + 1)
  have hb (y : ℝ) (hy : y ∈ Icc (-d) d) :
      ‖rsJnIntegrand sigma eta m (N + 1) y‖ ≤
        centralTaylorConstant sigma eta R (N + 1) * d ^ N *
          (d + 1 / (Real.sqrt 2 * Real.pi)) := by
    have hyd : |y| ≤ d := abs_le.mpr hy
    apply (jn_central_pointwise sigma he hR0 hR
      (by nlinarith [mul_le_mul_of_nonneg_left hyd rsSaddleScale_pos.le])
      hm0 hm1 N).trans
    have hex : Real.exp (-Real.pi * y ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y, Real.pi_pos])
    have hpow : |y| ^ N ≤ d ^ N := pow_le_pow_left₀ (abs_nonneg _) hyd N
    have hbase : centralTaylorConstant sigma eta R (N + 1) *
        Real.exp (-Real.pi * y ^ 2) * |y| ^ N ≤
        centralTaylorConstant sigma eta R (N + 1) * d ^ N := by
      apply (mul_le_mul (mul_le_mul_of_nonneg_left hex hC) hpow
        (pow_nonneg (abs_nonneg _) _) (by simpa using hC)).trans_eq
      ring
    exact mul_le_mul hbase (by linarith)
      (by positivity) (mul_nonneg hC (pow_nonneg hd N))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -d) (b := d) (fun y hy => hb y (by
      rw [uIoc_of_le (by linarith : -d ≤ d)] at hy
      exact ⟨hy.1.le, hy.2⟩))
  have habs : |2 * d| = 2 * d := abs_of_nonneg (by positivity)
  simpa only [sub_neg_eq_add, ← two_mul d, habs,
    centralIntervalBudget, mul_comm (2 * d)] using h

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
