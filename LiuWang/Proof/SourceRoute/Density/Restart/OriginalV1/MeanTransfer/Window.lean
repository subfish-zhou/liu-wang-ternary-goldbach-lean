import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Weight
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.RemoveWeight

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

theorem cosh_half_sq : Real.cosh (1 / 2) ^ 2 ≤ 1.272 := by
  have he : Real.exp (-(1 : ℝ)) ≤ 0.368 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith [Real.exp_one_gt_d9]
  have hh := Real.cosh_two_mul (1 / 2)
  norm_num at hh
  rw [Real.cosh_eq] at hh
  linarith [Real.exp_one_lt_d9, Real.cosh_sq_sub_sinh_sq (1 / 2)]

theorem source_window_cosine {y t : ℝ} (hy : 0 < y) (ht : |t| ≤ y) (sigma : ℝ) :
    ‖Complex.cos (((sigma : ℂ) + t * I) / (2 * (y : ℂ)))‖ ^ 2 ≤ 1.272 := by
  have hi : (((sigma : ℂ) + t * I) / (2 * (y : ℂ))).im = t / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp
  have hc := Strip.norm_cos_le_cosh (((sigma : ℂ) + t * I) / (2 * (y : ℂ)))
  rw [hi] at hc
  have hh : Real.cosh (t / (2 * y)) ≤ Real.cosh (1 / 2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * y)]
    norm_num
    exact (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr (by linarith)
  exact (pow_le_pow_left₀ (norm_nonneg _) (hc.trans hh) 2).trans cosh_half_sq

theorem source_window_ratio {sigma t : ℝ}
    (hs : sigma ∈ Icc (1 / 2) 1) (ht : 1 ≤ |t|) :
    ‖((sigma : ℂ) + t * I) / ((sigma : ℂ) + t * I - 1)‖ ^ 2 ≤ 2 := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  rw [norm_div, div_pow]
  have hnum : ‖(sigma : ℂ) + t * I‖ ^ 2 = sigma ^ 2 + t ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring
  have hden : ‖(sigma : ℂ) + t * I - 1‖ ^ 2 = (1 - sigma) ^ 2 + t ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hnum, hden]
  apply (div_le_iff₀ (by positivity : 0 < (1 - sigma) ^ 2 + t ^ 2)).mpr
  nlinarith [hs.1, hs.2, sq_nonneg (1 - sigma)]

theorem source_high_window {y sigma t : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y))
    (ht0 : 1 ≤ |t|) (ht : |t| ≤ y) :
    F y ((sigma : ℂ) + t * I) ≤
      (1.272 * 2) * ‖regularG y ((sigma : ℂ) + t * I)‖ ^ 2 := by
  have hy' : 10000 ≤ y := by linarith [(source_height_log_bounds hy).1]
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]; exact (Strip.delta_bounds hy').1
  have hr := source_window_ratio ⟨hs.1, by linarith [hs.2]⟩ ht0
  rw [norm_div, div_pow] at hr
  have hnum : ‖(sigma : ℂ) + t * I‖ ^ 2 = sigma ^ 2 + t ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring
  have hden : ‖(sigma : ℂ) + t * I - 1‖ ^ 2 = (1 - sigma) ^ 2 + t ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hnum, hden] at hr
  have hm := mul_le_mul hr (source_window_cosine (by linarith) ht sigma)
    (sq_nonneg _) (by norm_num)
  rw [sourceDelta_eq_strip_delta] at hs
  rw [MeanInterpolation.F_unweight hy' hs]
  have h := mul_le_mul_of_nonneg_right hm
    (sq_nonneg ‖regularG y ((sigma : ℂ) + t * I)‖)
  nlinarith

theorem equation_3_47 {y sigma : ℝ} (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) :
    M y sigma y ≤ M y sigma 1 + 1.272 * 2 * weightedMean y sigma := by
  have hy' : 10000 ≤ y := by linarith [(source_height_log_bounds hy).1]
  have hd : 0 < sourceDelta y := by
    rw [sourceDelta_eq_strip_delta]; exact (Strip.delta_bounds hy').1
  have hs1 : sigma ≠ 1 := by linarith [hs.2]
  let v (t : ℝ) := F y ((sigma : ℂ) + t * I)
  let w (t : ℝ) := ‖regularG y ((sigma : ℂ) + t * I)‖ ^ 2
  let small := (Icc (-1 : ℝ) 1).indicator v
  have hv : Continuous v := continuous_vertical_F y hs1
  have hw : Integrable w :=
    regularG_integrable hy ⟨hs.1, by linarith [hs.2]⟩
  have hvsmall : Integrable small :=
    hv.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (-y) y), v t ≤ small t + (1.272 * 2) * w t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    by_cases ht1 : t ∈ Icc (-1 : ℝ) 1
    · simp only [small, indicator_of_mem ht1]
      have : 0 ≤ w t := sq_nonneg _
      linarith
    · rw [show small t = 0 from indicator_of_notMem ht1 v]
      rw [zero_add]
      exact source_high_window hy hs (by
        have : ¬ |t| ≤ 1 := by simpa [abs_le] using ht1
        linarith) (abs_le.mpr ht)
  have hcomp := integral_mono_ae (hv.integrableOn_Icc)
    (hvsmall.integrableOn.add (hw.const_mul (1.272 * 2)).integrableOn) hpoint
  have hsmall : (∫ t in Icc (-y) y, small t) = M y sigma 1 := by
    rw [show small = (Icc (-1 : ℝ) 1).indicator v from rfl,
      setIntegral_indicator measurableSet_Icc,
      inter_eq_right.mpr (show Icc (-1 : ℝ) 1 ⊆ Icc (-y) y from
        fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    rfl
  have hwle : (∫ t in Icc (-y) y, w t) ≤ weightedMean y sigma :=
    setIntegral_le_integral hw (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  simp only [Pi.add_apply] at hcomp
  rw [integral_add hvsmall.integrableOn (hw.const_mul (1.272 * 2)).integrableOn,
    integral_const_mul, hsmall] at hcomp
  have hvmean : (∫ t in Icc (-y) y, v t) = M y sigma y := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rfl
  rw [hvmean] at hcomp
  linarith

theorem equation_3_47_with_small_window_paid {y sigma : ℝ}
    (hy : 10000 * Real.log 6 ≤ y)
    (hs : sigma ∈ Icc (1 / 2) (1 - sourceDelta y)) :
    M y sigma y ≤
      2 * 4.255 * y ^ (2 * (1 - sigma)) * (Real.log y) ^ (4 * sigma) +
        1.272 * 2 * weightedMean y sigma := by
  linarith [equation_3_47 hy hs, ChenArithmetic.equation_3_41 hy hs]

theorem equation_3_47_at_source_shift (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta y ≤ alpha) (ha1 : alpha < 1) :
    M y (alpha - sourceDelta y) y ≤
      2 * 4.255 * y ^ (2 * (1 - (alpha - sourceDelta y))) *
        (Real.log y) ^ (4 * (alpha - sourceDelta y)) +
        1.272 * 2 * weightedMean y (alpha - sourceDelta y) := by
  have hs := source_shift_in_lemma_3_5_domain ha ha1 (source_height_ge_log_six hy)
  rw [← sourceDelta_eq_strip_delta] at hs
  exact equation_3_47_with_small_window_paid (source_height_ge_log_six hy) hs

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
