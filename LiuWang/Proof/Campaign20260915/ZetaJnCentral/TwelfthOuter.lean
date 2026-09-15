import LiuWang.Proof.Campaign20260915.ZetaJnCentral.TwelfthRadius
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.PowerGaussianTail

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem twelfth_coefficient_scaled {eta : ℝ} (he : 44 ≤ eta) (n : ℕ) :
    ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ ≤
      150 / twelfthRadius eta ^ n := by
  have he0 : 0 < eta := by linarith
  have hs := rsSaddleScale_pos
  have hR := twelfthRadius_pos he0
  have h := smallCircle_coefficient (1 / 2) (mul_pos hs he0) (mul_pos hs hR)
    (R := rsSaddleScale * twelfthRadius eta)
    (by nlinarith [mul_le_mul_of_nonneg_left (twelfthRadius_data he).1 hs.le]) n
  have h' := h.trans (div_le_div_of_nonneg_right (twelfthRadius_majorant he0) (by positivity))
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hs]
  apply (mul_le_mul_of_nonneg_right h' (pow_nonneg hs.le n)).trans_eq
  rw [mul_pow]
  have hs0 := hs.ne'
  have hR0 := hR.ne'
  field_simp

theorem twelfth_outer_pointwise {eta y : ℝ} {m : ℕ} (he : 44 ≤ eta)
    (hyd : twelfthCutoff eta ≤ |y|) (hye : |y| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
      (Real.exp (3 / 8) * Real.exp (-Real.pi / 3 * y ^ 2) +
        600 * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
          Real.exp (-Real.pi / 2 * y ^ 2)) /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta)) := by
  have he0 : 0 < eta := by linarith
  have hd0 : 0 < twelfthCutoff eta := by linarith [(twelfthRadius_data he).2.1]
  have hR0 := twelfthRadius_pos he0
  have hn12 : (12 : ℝ) ≤ Real.pi * twelfthCutoff eta ^ 2 := by
    have hs : (100 / 9 : ℝ) ≤ twelfthCutoff eta ^ 2 := by
      nlinarith [(twelfthRadius_data he).2.1]
    nlinarith [Real.pi_gt_three]
  let z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)
  have hw : Real.exp (-Real.pi * y ^ 2) *
      ‖rsSaddleWeight (1 / 2) (rsSaddleScale * eta) z‖ ≤
      Real.exp (3 / 8) * Real.exp (-Real.pi / 3 * y ^ 2) := by
    have h := (re_le_norm (rsSaddleExponent (1 / 2) (rsSaddleScale * eta) z)).trans
      ((descent_exponent_norm (1 / 2) he0 hye).trans (descent_exponent_envelope (1 / 2) he0 hye))
    have hh := Real.exp_le_exp.mpr h
    rw [rsSaddleWeight, norm_exp]
    apply (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have ht (n : ℕ) (hn : n ∈ Finset.range 12) :
      Real.exp (-Real.pi * y ^ 2) *
        ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * z ^ n‖ ≤
      150 * (3 / 4 : ℝ) ^ n * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
        Real.exp (-Real.pi / 2 * y ^ 2) := by
    have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast (Finset.mem_range.mp hn).le
    have ha := powerGaussian_antitone n (by positivity : 0 < Real.pi / 2) hd0.le
      (by nlinarith : (n : ℝ) ≤ 2 * (Real.pi / 2) * twelfthCutoff eta ^ 2)
    have hm := ha (by simp) hyd hyd
    dsimp only at hm
    rw [sq_abs] at hm
    have hnorm : ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * z ^ n‖ =
        ‖rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ *
          |y| ^ n := by
      dsimp [z]
      rw [mul_pow, ← mul_assoc, norm_mul, norm_pow, rsDescentPoint_distance]
    rw [hnorm]
    apply (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (twelfth_coefficient_scaled he n) (by positivity))
      (Real.exp_pos _).le).trans
    have hm' := mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ 150 / twelfthRadius eta ^ n * Real.exp (-Real.pi / 2 * y ^ 2))
    have hyexp : Real.exp (-Real.pi / 2 * y ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2) =
        Real.exp (-Real.pi * y ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hratio : twelfthCutoff eta ^ n / twelfthRadius eta ^ n = (3 / 4 : ℝ) ^ n := by
      rw [twelfthCutoff, mul_pow]
      exact mul_div_cancel_right₀ _ (pow_ne_zero _ hR0.ne')
    calc
      _ = (150 / twelfthRadius eta ^ n * Real.exp (-Real.pi / 2 * y ^ 2)) *
          (|y| ^ n * Real.exp (-(Real.pi / 2) * y ^ 2)) := by
        simp only [neg_div]
        rw [← hyexp]
        ring
      _ ≤ _ := hm'
      _ = _ := by
        simp only [neg_div]
        have heq : (150 / twelfthRadius eta ^ n * Real.exp (-Real.pi / 2 * y ^ 2)) *
            (twelfthCutoff eta ^ n * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2)) =
            150 * (twelfthCutoff eta ^ n / twelfthRadius eta ^ n) *
              Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
              Real.exp (-Real.pi / 2 * y ^ 2) := by ring
        simp only [neg_div] at heq
        rw [heq, hratio]
  have hp : Real.exp (-Real.pi * y ^ 2) *
      ‖∑ n ∈ Finset.range 12, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * z ^ n‖ ≤
      600 * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2) := by
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le).trans
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum ht).trans
    have hsum : (∑ n ∈ Finset.range 12, (3 / 4 : ℝ) ^ n) ≤ 4 := by
      norm_num [Finset.sum_range_succ]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum
      (by norm_num : (0 : ℝ) ≤ 150))
      (by positivity : 0 ≤ Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
        Real.exp (-Real.pi / 2 * y ^ 2))
    simpa only [Finset.sum_mul, Finset.mul_sum, mul_assoc, show (150 : ℝ) * 4 = 600 by norm_num] using hh
  have hden := exterior_denominator_pos hd0
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul, rsSaddleRemainder]
  apply (mul_le_mul (exterior_gaussian_bound eta m hd0 hyd hm0 hm1)
    (norm_sub_le _ _) (norm_nonneg _) (div_nonneg (Real.exp_pos _).le hden.le)).trans
  calc
    _ = (Real.exp (-Real.pi * y ^ 2) * ‖rsSaddleWeight (1 / 2) (rsSaddleScale * eta) z‖ +
        Real.exp (-Real.pi * y ^ 2) *
          ‖∑ n ∈ Finset.range 12, rsSaddleCoefficient (1 / 2) (rsSaddleScale * eta) n * z ^ n‖) /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (add_le_add hw hp) hden.le

theorem norm_interval_twoGaussians {f : ℝ → ℂ} {b c B C d A : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 < d) (hAd : d ≤ A)
    (hf : ∀ y ∈ Icc d A, ‖f y‖ ≤ B * Real.exp (-b * y ^ 2) + C * Real.exp (-c * y ^ 2)) :
    ‖∫ y : ℝ in d..A, f y‖ ≤
      B * (Real.exp (-b * d ^ 2) / (2 * b * d)) +
        C * (Real.exp (-c * d ^ 2) / (2 * c * d)) := by
  have hiB : IntervalIntegrable (fun y : ℝ => B * Real.exp (-b * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ => B * Real.exp (-b * y ^ 2))).intervalIntegrable _ _
  have hiC : IntervalIntegrable (fun y : ℝ => C * Real.exp (-c * y ^ 2)) volume d A :=
    (by fun_prop : Continuous (fun y : ℝ => C * Real.exp (-c * y ^ 2))).intervalIntegrable _ _
  calc
    _ ≤ ∫ y : ℝ in d..A, B * Real.exp (-b * y ^ 2) + C * Real.exp (-c * y ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le hAd
        (Filter.Eventually.of_forall (fun y hy => hf y ⟨hy.1.le, hy.2⟩)) (hiB.add hiC)
    _ = B * (∫ y : ℝ in d..A, Real.exp (-b * y ^ 2)) +
        C * (∫ y : ℝ in d..A, Real.exp (-c * y ^ 2)) := by
      rw [intervalIntegral.integral_add hiB hiC, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (rsGaussian_tail_interval hb hd hAd) hB)
      (mul_le_mul_of_nonneg_left (rsGaussian_tail_interval hc hd hAd) hC)

def twelfthOuterBudget (eta : ℝ) : ℝ :=
  (Real.exp (3 / 8) * (3 / (Real.pi * twelfthCutoff eta)) *
      Real.exp (-Real.pi / 3 * twelfthCutoff eta ^ 2) +
    1200 / (Real.pi * twelfthCutoff eta) * Real.exp (-Real.pi * twelfthCutoff eta ^ 2)) /
      (1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta))

theorem jn_twelfth_outer {eta : ℝ} {m : ℕ} (he : 44 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (twelfthCutoff eta)..(eta / 2), rsJnIntegrand (1 / 2) eta m 12 y‖ +
      ‖∫ y : ℝ in (-eta / 2)..(-twelfthCutoff eta), rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
        twelfthOuterBudget eta := by
  have hd : 0 < twelfthCutoff eta := by linarith [(twelfthRadius_data he).2.1]
  have hdA := (twelfthRadius_data he).2.2.1
  have hden := exterior_denominator_pos hd
  let den := 1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta)
  have hb (e : ℝ) (heps : |e| = 1) :
      ‖∫ y : ℝ in (twelfthCutoff eta)..(eta / 2), rsJnIntegrand (1 / 2) eta m 12 (e * y)‖ ≤
      (Real.exp (3 / 8) / den) *
        (Real.exp (-(Real.pi / 3) * twelfthCutoff eta ^ 2) / (2 * (Real.pi / 3) * twelfthCutoff eta)) +
      (600 * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) / den) *
        (Real.exp (-(Real.pi / 2) * twelfthCutoff eta ^ 2) / (2 * (Real.pi / 2) * twelfthCutoff eta)) := by
    apply norm_interval_twoGaussians (by positivity) (by positivity)
      (div_nonneg (Real.exp_pos _).le hden.le)
      (div_nonneg (by positivity) hden.le) hd hdA
    intro y hy
    have hn : |e * y| = y := by rw [abs_mul, heps, abs_of_pos (hd.trans_le hy.1), one_mul]
    have hs : (e * y) ^ 2 = y ^ 2 := by rw [← sq_abs (e * y), hn]
    have h := twelfth_outer_pointwise he (y := e * y)
      (by rw [hn]; exact hy.1) (by rw [hn]; exact hy.2) hm0 hm1
    rw [hs] at h
    exact h.trans_eq (by simp only [neg_div]; ring)
  have hp := hb 1 (by norm_num)
  have hn := hb (-1) (by norm_num)
  simp only [one_mul] at hp
  simp only [neg_one_mul, intervalIntegral.integral_comp_neg, neg_div] at hn
  simp only [neg_div] at hp ⊢
  apply (add_le_add hp hn).trans_eq
  have hx : Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
      Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) =
      Real.exp (-Real.pi * twelfthCutoff eta ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold twelfthOuterBudget
  rw [← hx]
  dsimp [den]
  simp only [neg_div]
  ring

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
