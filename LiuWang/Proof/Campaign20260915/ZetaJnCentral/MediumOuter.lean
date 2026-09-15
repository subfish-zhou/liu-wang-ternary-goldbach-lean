import LiuWang.Proof.Campaign20260915.ZetaJnCentral.MediumCircleTaylor
import LiuWang.Proof.Campaign20260915.ZetaJnCentral.TwelfthOuter

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem jn_outer_from_coefficients (sigma : ℝ) {eta y d R M S : ℝ} {m N : ℕ}
    (he : 0 < eta) (hd : 0 < d) (hR : 0 < R) (hM : 0 ≤ M)
    (hN : (N : ℝ) ≤ Real.pi * d ^ 2) (hyd : d ≤ |y|) (hye : |y| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1)
    (hcoeff : ∀ n ∈ Finset.range N,
      ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ ≤ M / R ^ n)
    (hsum : (∑ n ∈ Finset.range N, (d / R) ^ n) ≤ S) :
    ‖rsJnIntegrand sigma eta m N y‖ ≤
      (Real.exp (3 / 4 * |sigma - 1|) * Real.exp (-Real.pi / 3 * y ^ 2) +
        M * S * Real.exp (-Real.pi / 2 * d ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2)) /
          (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) := by
  let z := (rsSaddleScale : ℂ) * (rsDescentPoint eta y - eta)
  have hw : Real.exp (-Real.pi * y ^ 2) * ‖rsSaddleWeight sigma (rsSaddleScale * eta) z‖ ≤
      Real.exp (3 / 4 * |sigma - 1|) * Real.exp (-Real.pi / 3 * y ^ 2) := by
    have h := (re_le_norm (rsSaddleExponent sigma (rsSaddleScale * eta) z)).trans
      ((descent_exponent_norm sigma he hye).trans (descent_exponent_envelope sigma he hye))
    rw [rsSaddleWeight, norm_exp]
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ht (n : ℕ) (hn : n ∈ Finset.range N) :
      Real.exp (-Real.pi * y ^ 2) * ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * z ^ n‖ ≤
        M * (d / R) ^ n * Real.exp (-Real.pi / 2 * d ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2) := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
    have ha := powerGaussian_antitone n (by positivity : 0 < Real.pi / 2) hd.le
      (by nlinarith : (n : ℝ) ≤ 2 * (Real.pi / 2) * d ^ 2)
    have hm := ha (by simp) hyd hyd
    dsimp only at hm
    rw [sq_abs] at hm
    have hnorm : ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * z ^ n‖ =
        ‖rsSaddleCoefficient sigma (rsSaddleScale * eta) n * (rsSaddleScale : ℂ) ^ n‖ * |y| ^ n := by
      dsimp [z]
      rw [mul_pow, ← mul_assoc, norm_mul, norm_pow, rsDescentPoint_distance]
    rw [hnorm]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcoeff n hn) (by positivity))
      (Real.exp_pos _).le).trans
    have hm' := mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ M / R ^ n * Real.exp (-Real.pi / 2 * y ^ 2))
    have hyexp : Real.exp (-Real.pi / 2 * y ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2) =
        Real.exp (-Real.pi * y ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (M / R ^ n * Real.exp (-Real.pi / 2 * y ^ 2)) *
          (|y| ^ n * Real.exp (-(Real.pi / 2) * y ^ 2)) := by
        simp only [neg_div]
        rw [← hyexp]
        ring
      _ ≤ _ := hm'
      _ = _ := by
        simp only [neg_div, div_pow]
        ring
  have hp : Real.exp (-Real.pi * y ^ 2) *
      ‖∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n * z ^ n‖ ≤
      M * S * Real.exp (-Real.pi / 2 * d ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2) := by
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le).trans
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum ht).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hM)
      (by positivity : 0 ≤ Real.exp (-Real.pi / 2 * d ^ 2) * Real.exp (-Real.pi / 2 * y ^ 2))
    simpa only [Finset.sum_mul, Finset.mul_sum, mul_assoc] using hh
  have hden := exterior_denominator_pos hd
  rw [rsJnIntegrand, norm_mul, norm_mul, rsDescentDirection_norm, one_mul, rsSaddleRemainder]
  apply (mul_le_mul (exterior_gaussian_bound eta m hd hyd hm0 hm1)
    (norm_sub_le _ _) (norm_nonneg _) (div_nonneg (Real.exp_pos _).le hden.le)).trans
  calc
    _ = (Real.exp (-Real.pi * y ^ 2) * ‖rsSaddleWeight sigma (rsSaddleScale * eta) z‖ +
        Real.exp (-Real.pi * y ^ 2) *
          ‖∑ n ∈ Finset.range N, rsSaddleCoefficient sigma (rsSaddleScale * eta) n * z ^ n‖) /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * d)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (add_le_add hw hp) hden.le

theorem medium_outer_pointwise {eta y : ℝ} {m : ℕ} (he : 11 ≤ eta)
    (hyd : twelfthCutoff eta ≤ |y|) (hye : |y| ≤ eta / 2)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
      (Real.exp (3 / 8) * Real.exp (-Real.pi / 3 * y ^ 2) +
        3000 * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
          Real.exp (-Real.pi / 2 * y ^ 2)) /
        (1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta)) := by
  have he0 : 0 < eta := by linarith
  have hR := twelfthRadius_pos he0
  have hd : 0 < twelfthCutoff eta := by linarith [(mediumRadius_data he).2.1]
  have hn : (12 : ℝ) ≤ Real.pi * twelfthCutoff eta ^ 2 := by
    have hs : (441 / 100 : ℝ) ≤ twelfthCutoff eta ^ 2 := by nlinarith [(mediumRadius_data he).2.1]
    nlinarith [Real.pi_gt_three]
  have hsum : (∑ n ∈ Finset.range 12, (twelfthCutoff eta / twelfthRadius eta) ^ n) ≤ 4 := by
    rw [twelfthCutoff, mul_div_cancel_right₀ _ hR.ne']
    norm_num [Finset.sum_range_succ]
  have h := jn_outer_from_coefficients (1 / 2) he0 hd hR (by norm_num : (0 : ℝ) ≤ 750)
    hn hyd hye hm0 hm1 (fun n _ => mediumCircle_coefficient he n) hsum
  norm_num only [show 3 / 4 * |(1 / 2 : ℝ) - 1| = 3 / 8 by norm_num,
    show (750 : ℝ) * 4 = 3000 by norm_num] at h
  exact h

def mediumOuterBudget (eta : ℝ) : ℝ :=
  (Real.exp (3 / 8) * (3 / (Real.pi * twelfthCutoff eta)) *
      Real.exp (-Real.pi / 3 * twelfthCutoff eta ^ 2) +
    6000 / (Real.pi * twelfthCutoff eta) * Real.exp (-Real.pi * twelfthCutoff eta ^ 2)) /
      (1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta))

theorem jn_medium_outer {eta : ℝ} {m : ℕ} (he : 11 ≤ eta)
    (hm0 : 0 ≤ eta - m) (hm1 : eta - m ≤ 1) :
    ‖∫ y : ℝ in (twelfthCutoff eta)..(eta / 2), rsJnIntegrand (1 / 2) eta m 12 y‖ +
      ‖∫ y : ℝ in (-eta / 2)..(-twelfthCutoff eta), rsJnIntegrand (1 / 2) eta m 12 y‖ ≤
        mediumOuterBudget eta := by
  have hd : 0 < twelfthCutoff eta := by linarith [(mediumRadius_data he).2.1]
  have hdA := (mediumRadius_data he).2.2.1
  have hden := exterior_denominator_pos hd
  let den := 1 - Real.exp (-Real.sqrt 2 * Real.pi * twelfthCutoff eta)
  have hb (e : ℝ) (heps : |e| = 1) :
      ‖∫ y : ℝ in (twelfthCutoff eta)..(eta / 2), rsJnIntegrand (1 / 2) eta m 12 (e * y)‖ ≤
      (Real.exp (3 / 8) / den) *
        (Real.exp (-(Real.pi / 3) * twelfthCutoff eta ^ 2) / (2 * (Real.pi / 3) * twelfthCutoff eta)) +
      (3000 * Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) / den) *
        (Real.exp (-(Real.pi / 2) * twelfthCutoff eta ^ 2) / (2 * (Real.pi / 2) * twelfthCutoff eta)) := by
    apply norm_interval_twoGaussians (by positivity) (by positivity)
      (div_nonneg (Real.exp_pos _).le hden.le) (div_nonneg (by positivity) hden.le) hd hdA
    intro y hy
    have hn : |e * y| = y := by rw [abs_mul, heps, abs_of_pos (hd.trans_le hy.1), one_mul]
    have hs : (e * y) ^ 2 = y ^ 2 := by rw [← sq_abs (e * y), hn]
    have h := medium_outer_pointwise he (y := e * y)
      (by rw [hn]; exact hy.1) (by rw [hn]; exact hy.2) hm0 hm1
    rw [hs] at h
    exact h.trans_eq (by simp only [neg_div]; ring)
  have hp := hb 1 (by norm_num)
  have hn := hb (-1) (by norm_num)
  simp only [one_mul, neg_div] at hp
  simp only [neg_one_mul, intervalIntegral.integral_comp_neg, neg_div] at hn
  simp only [neg_div]
  apply (add_le_add hp hn).trans_eq
  have hx : Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) *
      Real.exp (-Real.pi / 2 * twelfthCutoff eta ^ 2) = Real.exp (-Real.pi * twelfthCutoff eta ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold mediumOuterBudget
  rw [← hx]
  dsimp [den]
  simp only [neg_div]
  ring

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
