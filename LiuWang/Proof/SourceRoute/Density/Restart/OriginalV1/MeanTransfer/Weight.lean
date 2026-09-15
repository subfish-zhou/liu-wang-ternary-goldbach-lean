import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.Consumer
import LiuWang.Proof.GlobalZeroDensity.Strip.FullAxis

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

theorem source_domain {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    10000 ≤ y ∧ 0 < sigma ∧ sigma ≤ 2 ∧ sigma < Real.pi * y := by
  have hy' := (source_height_log_bounds hy).1
  have hd := sourceDelta_le_twelfth (show 10000 ≤ y by linarith)
  refine ⟨by linarith, by linarith [hs.1], by linarith [hs.2], ?_⟩
  nlinarith [hs.2, Real.pi_gt_three]

theorem regularG_integrable {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    Integrable (fun t : ℝ => ‖regularG y ((sigma : ℂ) + t * I)‖ ^ 2) := by
  rw [sourceDelta_eq_strip_delta] at hs
  exact Strip.regularG_strip_integrable (by linarith [(source_height_log_bounds hy).1]) hs

theorem regularG_eq_original_ae (y sigma : ℝ) :
    (fun t : ℝ => regularG y ((sigma : ℂ) + t * I)) =ᵐ[volume]
      (fun t : ℝ => g y ((sigma : ℂ) + t * I)) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  apply regularG_eq_g
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact ht hi

theorem cosh_sq_lower (x : ℝ) :
    (Real.exp (2 * |x|) + 2) / 4 ≤ Real.cosh x ^ 2 := by
  have he : Real.exp |x| * Real.exp (-|x|) = 1 := by rw [← Real.exp_add]; simp
  have hp : Real.exp (2 * |x|) = Real.exp |x| ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [← Real.cosh_abs, Real.cosh_eq, hp]
  nlinarith [sq_nonneg (Real.exp (-|x|))]

theorem cosine_source_lower {z : ℂ} (hz : |z.re| ≤ 1 / 10000) :
    (2 + Real.exp (2 * |z.im|)) ≤
      (4 + (10 : ℝ) ^ (-7 : ℤ)) * ‖Complex.cos z‖ ^ 2 := by
  have hx2 : z.re ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := by
    nlinarith [sq_abs z.re, mul_nonneg (sub_nonneg.mpr hz) (abs_nonneg z.re)]
  have hc : (1 - 1 / 200000000 : ℝ) ≤ Real.cos z.re := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := z.re)]
  have hre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp [Complex.cos_ofReal_re]
  have hn : (1 - 1 / 200000000 : ℝ) * Real.cosh z.im ≤ ‖Complex.cos z‖ := by
    have h := mul_le_mul_of_nonneg_right hc (Real.cosh_pos z.im).le
    rw [← hre] at h
    exact h.trans (Complex.re_le_norm _)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤
    (1 - 1 / 200000000 : ℝ) * Real.cosh z.im) hn 2
  rw [mul_pow] at hsq
  have hlow := cosh_sq_lower z.im
  have hm := mul_le_mul_of_nonneg_left hlow
    (by norm_num : (0 : ℝ) ≤ (1 - 1 / 200000000) ^ 2)
  norm_num at hsq hm ⊢
  nlinarith [sq_nonneg ‖Complex.cos z‖]

theorem source_cosine_lower {y sigma t : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y)) :
    2 + Real.exp (|t| / y) ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      ‖Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 := by
  obtain ⟨hy', hs0, hs2, _⟩ := source_domain hy hs
  have hz : |(((sigma : ℂ) + t * I) / (2 * (y : ℂ))).re| ≤ 1 / 10000 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, zero_mul, sub_self, add_zero]
    rw [abs_of_pos (div_pos hs0 (by positivity))]
    apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
    nlinarith
  have hi : 2 * |(((sigma : ℂ) + t * I) / (2 * (y : ℂ))).im| = |t| / y := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp [abs_div, abs_of_pos (show 0 < y by linarith), abs_mul]
    ring
  simpa only [hi] using cosine_source_lower hz

theorem regularG_source_envelope {y sigma t : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 + sourceDelta y))
    (hp : (sigma : ℂ) + t * I ≠ 1) :
    ‖regularG y ((sigma : ℂ) + t * I)‖ ^ 2 ≤
      (4 + (10 : ℝ) ^ (-7 : ℤ)) *
        (F y ((sigma : ℂ) + t * I) / (2 + Real.exp (|t| / y))) := by
  let s := (sigma : ℂ) + t * I
  let c := ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2
  have hs0 : 0 < ‖s‖ := by
    have h := Complex.re_le_norm s
    simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, zero_mul, sub_self, add_zero] at h
    linarith [hs.1]
  have hratio : ‖s - 1‖ ^ 2 / ‖s‖ ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hs0)).mpr
    exact pow_le_pow_left₀ (norm_nonneg _) (Strip.norm_sub_one_le (by simpa [s] using hs.1)) 2
  have hcos := source_cosine_lower hy hs (t := t)
  have hc : 0 < c := by dsimp [c, s]; nlinarith [Real.exp_pos (|t| / y)]
  have hi : 1 / c ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) / (2 + Real.exp (|t| / y)) := by
    apply (div_le_div_iff₀ hc (by positivity)).mpr
    simpa [c, s] using hcos
  have he : ‖regularG y s‖ ^ 2 = (‖s - 1‖ ^ 2 / ‖s‖ ^ 2) * (F y s / c) := by
    rw [regularG_eq_g hp, g, norm_mul, norm_div, norm_mul, mul_pow, div_pow, mul_pow]
    dsimp [F, c]; ring
  rw [he]
  calc
    _ ≤ F y s / c := by
      simpa using mul_le_mul_of_nonneg_right hratio (by dsimp [F]; positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hi (show 0 ≤ F y s from sq_nonneg _)
      dsimp [s] at h ⊢
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
