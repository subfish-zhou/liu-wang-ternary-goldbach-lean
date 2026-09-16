import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFiftyMain
import LiuWang.Proof.Campaign20260915.ZetaValidation.HighOrderEvaluation

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

private theorem bernoulli_four_value : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]

theorem backlund_bernoulli_four_bound {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |normalizedBernoulli 4 x| ≤ 1 / 720 := by
  have he : normalizedBernoulli 4 x = (x * (1 - x)) ^ 2 / 24 - 1 / 720 := by
    norm_num [normalizedBernoulli_expansion, sum_range_succ, bernoulli_four_value, Nat.choose]
    ring
  have hp : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
  have hp' : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hs : (x * (1 - x)) ^ 2 ≤ 1 / 16 := by nlinarith
  rw [he, abs_le]
  constructor <;> nlinarith [sq_nonneg (x * (1 - x))]

theorem backlund_bernoulli_four_tail {s : ℂ} (hs : 0 < s.re)
    {a : ℝ} (ha : 0 < a) :
    ‖∫ u in Ioi a, bernoulliKernel 4 s u‖ ≤
      a ^ (-s.re - 3) / (720 * (s.re + 3)) := by
  calc
    _ ≤ ∫ u in Ioi a, (1 / 720 : ℝ) * u ^ (-s.re - 4) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 4 < -1) ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [bernoulliKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hu)]
      simp only [sub_re, neg_re, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_right
        (backlund_bernoulli_four_bound ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩)
        (Real.rpow_nonneg (ha.trans hu).le _)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
      rw [show -s.re - 4 + 1 = -s.re - 3 by ring,
        show -s.re - 3 = -(s.re + 3) by ring, neg_div_neg_eq]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem ten_decay {σ : ℝ} (hσ : 1 / 2 ≤ σ) (k : ℕ) :
    (10 : ℝ) ^ (-σ - k) ≤ 10 / (31 * 10 ^ k) := by
  have hs : 31 / 10 ≤ Real.sqrt 10 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg 10]
  have hp : (10 : ℝ) ^ (-σ) ≤ 10 / 31 := by
    calc
      _ ≤ (10 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / Real.sqrt 10 := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]
      _ ≤ 10 / 31 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
  have h := div_le_div_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ 10 ^ k)
  exact h.trans_eq (by ring)

private theorem ten_cpow_norm (z : ℂ) :
    ‖(10 : ℂ) ^ z‖ = (10 : ℝ) ^ z.re := by
  rw [show (10 : ℂ) = ((10 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 10)]

private theorem fifty_norms {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : s.im = 50) :
    ‖s‖ ≤ 51 ∧ 50 ≤ ‖s - 1‖ := by
  constructor
  · have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith), ht] at h
    norm_num at h
    linarith
  · have h := abs_im_le_norm (s - 1)
    simpa [ht] using h

theorem backlund_fifty_em_tail {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : s.im = 50) :
    ‖riemannZeta s - eulerMaclaurinApprox s 10 3‖ ≤ 11 / 10 := by
  have hs1 : s ≠ 1 := by intro he; rw [he] at ht; norm_num at ht
  rw [zeta_sub_eulerMaclaurinApprox 3 (by linarith) hs1 (by norm_num), norm_mul, norm_neg]
  have hn := (fifty_norms hs hs' ht).1
  have hp := norm_risingProduct_le s 3
  have hp' : ‖risingProduct s 4‖ ≤ (54 : ℝ) ^ 4 :=
    hp.trans (pow_le_pow_left₀ (by positivity) (by norm_num; linarith) 4)
  have hb := backlund_bernoulli_four_tail (s := s) (by linarith) (a := 10) (by norm_num)
  have hd : (10 : ℝ) ^ (-s.re - 3) ≤ 1 / 3100 := by
    exact (ten_decay hs 3).trans_eq (by norm_num)
  have hb' : ‖∫ u in Ioi (10 : ℝ), bernoulliKernel 4 s u‖ ≤ 1 / 7812000 := by
    refine hb.trans ?_
    calc
      _ ≤ (1 / 3100 : ℝ) / (720 * (s.re + 3)) :=
        div_le_div_of_nonneg_right hd (by linarith)
      _ ≤ (1 / 3100 : ℝ) / 2520 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = _ := by norm_num
  have h := mul_le_mul hp' hb' (norm_nonneg _) (by positivity)
  norm_num at h
  exact h.trans (by norm_num)

theorem backlund_fifty_zeta_bound {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : s.im = 50) :
    ‖riemannZeta s‖ < 7 / 2 := by
  have hn := fifty_norms hs hs' ht
  have hN : (10 : ℝ) ^ (1 - s.re) ≤ 16 / 5 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 10)
      (by linarith : 1 - s.re ≤ 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    have hsqrt : Real.sqrt 10 ≤ 16 / 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg 10]
    exact h.trans hsqrt
  have hdec1 : (10 : ℝ) ^ (-s.re - 1) ≤ 1 / 31 := by
    have h := ten_decay hs 1
    norm_num only [Nat.cast_one] at h
    exact h
  have hdec3 : (10 : ℝ) ^ (-s.re - 3) ≤ 1 / 3100 := by
    exact (ten_decay hs 3).trans_eq (by norm_num)
  have ht0 : ‖(10 : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 8 / 125 := by
    rw [norm_div, ten_cpow_norm]
    simp only [sub_re, one_re]
    calc
      _ ≤ (16 / 5 : ℝ) / 50 :=
        div_le_div₀ (by positivity) hN (by norm_num) hn.2
      _ = _ := by norm_num
  have ht1 : ‖s * (1 / 12 : ℂ) * (10 : ℂ) ^ (-s - 1)‖ ≤ 7 / 50 := by
    rw [norm_mul, norm_mul, ten_cpow_norm]
    norm_num only [norm_div, norm_one, norm_ofNat, sub_re, neg_re, one_re]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hn.1 (by norm_num : (0 : ℝ) ≤ 1 / 12))
      hdec1 (by positivity) (by norm_num)
    norm_num at h
    exact h.trans (by norm_num)
  have ht3 : ‖risingProduct s 3 * (-1 / 720 : ℂ) * (10 : ℂ) ^ (-s - 3)‖ ≤ 7 / 100 := by
    rw [norm_mul, norm_mul, ten_cpow_norm]
    norm_num only [norm_div, norm_neg, norm_one, norm_ofNat, sub_re, neg_re]
    have hr : ‖risingProduct s 3‖ ≤ (53 : ℝ) ^ 3 :=
      (norm_risingProduct_le s 2).trans (pow_le_pow_left₀ (by positivity) (by norm_num; linarith [hn.1]) 3)
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 1 / 720))
      hdec3 (by positivity) (by norm_num)
    norm_num at h
    exact h.trans (by norm_num)
  have he : eulerMaclaurinApprox s 10 3 =
      (backlundFiftyMain s + (10 : ℂ) ^ (1 - s) / (s - 1)) +
        s * (1 / 12 : ℂ) * (10 : ℂ) ^ (-s - 1) +
          risingProduct s 3 * (-1 / 720 : ℂ) * (10 : ℂ) ^ (-s - 3) := by
    rw [backlundFiftyMain_partial_sum]
    norm_num [eulerMaclaurinApprox, normalizedBernoulli_zero, bernoulli_four_value,
      risingProduct, prod_range_succ, abelApprox]
    ring
  have ha := norm_add_le (backlundFiftyMain s) ((10 : ℂ) ^ (1 - s) / (s - 1))
  have hb := norm_add_le
    (backlundFiftyMain s + (10 : ℂ) ^ (1 - s) / (s - 1))
    (s * (1 / 12 : ℂ) * (10 : ℂ) ^ (-s - 1))
  have hc := norm_add_le
    ((backlundFiftyMain s + (10 : ℂ) ^ (1 - s) / (s - 1)) +
      s * (1 / 12 : ℂ) * (10 : ℂ) ^ (-s - 1))
    (risingProduct s 3 * (-1 / 720 : ℂ) * (10 : ℂ) ^ (-s - 3))
  have hz := norm_add_le (riemannZeta s - eulerMaclaurinApprox s 10 3)
    (eulerMaclaurinApprox s 10 3)
  rw [sub_add_cancel] at hz
  have herr := backlund_fifty_em_tail hs hs' ht
  rw [← he] at hc
  linarith [backlundFiftyMain_norm_lt hs ht]

#print axioms backlund_bernoulli_four_bound
#print axioms backlund_bernoulli_four_tail
#print axioms backlund_fifty_em_tail
#print axioms backlund_fifty_zeta_bound

end LiuWang.Proof.Campaign20260915.RosserCount
