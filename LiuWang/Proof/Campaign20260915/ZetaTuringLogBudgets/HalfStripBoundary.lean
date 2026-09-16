import LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets.AnalyticStripWeight

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

def sourceBottomLogWeight (T x : ℝ) : ℝ :=
  32 * Real.exp (128 * Real.pi - T) * Real.cos (x - 7 / 8)

def sourceBottomBarrier (s : ℂ) : ℂ :=
  Complex.exp (32 * Complex.exp (Complex.I *
    (s - 7 / 8 - (128 * Real.pi : ℂ) * Complex.I)))

def sourceHalfStripQuotient (s : ℂ) : ℂ :=
  sourceStripQuotient s / sourceBottomBarrier s

theorem sourceStripBoundaryExponent_re (s : ℂ) :
    (sourceStripBoundaryExponent s).re =
      (5 / 4 - s.re) / (3 / 4) * Real.log (253 / 100 : ℝ) +
        (s.re - 1 / 2) / (3 / 4) * realLogZeta (5 / 4) := by
  norm_num [sourceStripBoundaryExponent, div_re, div_im, mul_re, mul_im, normSq_apply]
  ring

theorem sourceStripQuotient_norm_le_zeta {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 1 ≤ s.im) :
    ‖sourceStripQuotient s‖ ≤ ‖riemannZeta s‖ := by
  have hs0 : 0 < s.re := by linarith [hs.1]
  have ht0 : 0 < s.im := by linarith
  have hn1 : 1 ≤ ‖s‖ := ht.trans ((le_abs_self _).trans (Complex.abs_im_le_norm s))
  have hD : ‖s‖ ≤ ‖sourceStripNormalizer s‖ := by
    calc
      ‖s‖ = ‖s‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ‖s‖ ^ (17 / 12 - s.re / 3) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hs.2])
      _ ≤ _ := sourceStripNormalizer_norm_lower hs0 ht0
  have hB : 0 ≤ (sourceStripBoundaryExponent s).re := by
    rw [sourceStripBoundaryExponent_re]
    have h0 : 0 ≤ (5 / 4 : ℝ) - s.re := by linarith [hs.2]
    have h1 : 0 ≤ s.re - (1 / 2 : ℝ) := by linarith [hs.1]
    have hK : 0 ≤ Real.log (253 / 100 : ℝ) := Real.log_nonneg (by norm_num)
    have hL := realLogZeta_nonneg (by norm_num : (1 : ℝ) < 5 / 4)
    positivity
  have hden := hD.trans (le_mul_of_one_le_right (norm_nonneg _)
    (Real.one_le_exp hB))
  have hnorm : ‖s - 1‖ ≤ ‖s‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero]
    nlinarith [hs.1]
  rw [sourceStripQuotient, norm_div, norm_mul, norm_mul, Complex.norm_exp]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr (sourceStripNormalizer_ne_zero s))
    (Real.exp_pos _))).mpr
  nlinarith [mul_le_mul_of_nonneg_right (hnorm.trans hden) (norm_nonneg (riemannZeta s))]

theorem sourceStripQuotient_linear_growth {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 1 ≤ s.im) :
    ‖sourceStripQuotient s‖ < 8 + 2 * s.im := by
  have h := norm_riemannZeta_lt_linear_im_on_strip s
    ⟨hs.1, by linarith [hs.2]⟩ (ht.trans (le_abs_self _))
  rw [abs_of_nonneg (by linarith : 0 ≤ s.im)] at h
  exact (sourceStripQuotient_norm_le_zeta hs ht).trans_lt h

theorem sourceBottom_cos_lower {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) :
    (1 / 2 : ℝ) ≤ Real.cos (x - 7 / 8) := by
  have hs := mul_nonneg (show 0 ≤ x - 1 / 2 by linarith [hx.1])
    (show 0 ≤ 5 / 4 - x by linarith [hx.2])
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := x - 7 / 8)]

theorem sourceBottomBarrier_ne_zero (s : ℂ) : sourceBottomBarrier s ≠ 0 :=
  Complex.exp_ne_zero _

theorem sourceBottomBarrier_differentiable : Differentiable ℂ sourceBottomBarrier := by
  unfold sourceBottomBarrier
  fun_prop

theorem sourceBottomBarrier_norm (s : ℂ) :
    ‖sourceBottomBarrier s‖ = Real.exp (sourceBottomLogWeight s.im s.re) := by
  rw [sourceBottomBarrier, Complex.norm_exp]
  congr 1
  simp [sourceBottomLogWeight, Complex.exp_re, mul_re, mul_im]
  ring

theorem sourceBottomBarrier_norm_ge_one {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) :
    1 ≤ ‖sourceBottomBarrier s‖ := by
  rw [sourceBottomBarrier_norm]
  apply Real.one_le_exp
  unfold sourceBottomLogWeight
  exact mul_nonneg (by positivity) (by linarith [sourceBottom_cos_lower hs])

theorem sourceBottomBarrier_bottom_lower {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : s.im = 128 * Real.pi) :
    1032 ≤ ‖sourceBottomBarrier s‖ := by
  have h := Real.pow_div_factorial_le_exp (16 : ℝ) (by norm_num) 4
  norm_num at h
  have he : (1032 : ℝ) ≤ Real.exp 16 := by linarith
  rw [sourceBottomBarrier_norm, sourceBottomLogWeight, ht, sub_self, Real.exp_zero, mul_one]
  exact he.trans (Real.exp_le_exp.mpr (by linarith [sourceBottom_cos_lower hs]))

theorem sourceHalfStripQuotient_differentiableAt {s : ℂ} (hs : 0 < s.re) (ht : 0 < s.im) :
    DifferentiableAt ℂ sourceHalfStripQuotient s :=
  (sourceStripQuotient_differentiableAt hs ht).div
    sourceBottomBarrier_differentiable.differentiableAt (sourceBottomBarrier_ne_zero s)

theorem sourceHalfStripQuotient_norm_le {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) :
    ‖sourceHalfStripQuotient s‖ ≤ ‖sourceStripQuotient s‖ := by
  rw [sourceHalfStripQuotient, norm_div]
  exact div_le_self (norm_nonneg _) (sourceBottomBarrier_norm_ge_one hs)

theorem sourceHalfStripQuotient_right_boundary {s : ℂ}
    (hs : s.re = 5 / 4) (ht : 0 < s.im) : ‖sourceHalfStripQuotient s‖ ≤ 1 :=
  (sourceHalfStripQuotient_norm_le (by rw [hs]; constructor <;> norm_num)).trans
    (sourceStripQuotient_right_boundary hs ht)

theorem sourceHalfStripQuotient_bottom_boundary {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : s.im = 128 * Real.pi) :
    ‖sourceHalfStripQuotient s‖ ≤ 1 := by
  have hi : 1 ≤ s.im := by rw [ht]; linarith [Real.pi_gt_three]
  have h := sourceStripQuotient_linear_growth hs hi
  rw [ht] at h
  have hq : ‖sourceStripQuotient s‖ ≤ 1032 := by linarith [Real.pi_lt_four]
  rw [sourceHalfStripQuotient, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (sourceBottomBarrier_ne_zero s))).mpr
    (hq.trans (sourceBottomBarrier_bottom_lower hs ht))

theorem sourceHalfStripQuotient_linear_growth {s : ℂ}
    (hs : s.re ∈ Set.Icc (1 / 2 : ℝ) (5 / 4)) (ht : 1 ≤ s.im) :
    ‖sourceHalfStripQuotient s‖ < 8 + 2 * s.im :=
  (sourceHalfStripQuotient_norm_le hs).trans_lt (sourceStripQuotient_linear_growth hs ht)

theorem integral_sourceBottomLogWeight (T : ℝ) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceBottomLogWeight T x) ≤
      24 * Real.exp (128 * Real.pi - T) := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)
    ((by unfold sourceBottomLogWeight; fun_prop :
      Continuous (sourceBottomLogWeight T)).intervalIntegrable _ _) intervalIntegrable_const
    (fun x _ => mul_le_of_le_one_right
      (by positivity : 0 ≤ 32 * Real.exp (128 * Real.pi - T)) (Real.cos_le_one (x - 7 / 8)))
  rw [intervalIntegral.integral_const] at h
  norm_num at h
  convert! h using 1
  ring

theorem integral_sourceBottomLogWeight_original_budget {T : ℝ} (hT : 168 * Real.pi < T) :
    (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceBottomLogWeight T x) < 1 / 1000000000 := by
  have hx : 128 * Real.pi - T < -120 := by linarith [Real.pi_gt_three]
  have hp := Real.pow_div_factorial_le_exp (120 : ℝ) (by norm_num) 8
  norm_num at hp
  have he : (24 : ℝ) / Real.exp 120 < 1 / 1000000000 := by
    rw [div_lt_iff₀ (Real.exp_pos _)]
    linarith
  calc
    _ ≤ 24 * Real.exp (128 * Real.pi - T) := integral_sourceBottomLogWeight T
    _ ≤ 24 * Real.exp (-120) := by gcongr
    _ < _ := by rw [Real.exp_neg, ← div_eq_mul_inv]; exact he

theorem sourceStrip_total_geometric_budget {T : ℝ} (hT : 168 * Real.pi < T) :
    681 / (2048 * T ^ 2) +
      (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceStripArgumentCorrection T x) +
      (∫ x in (1 / 2 : ℝ)..(5 / 4), sourceBottomLogWeight T x) < 1 / 500000 := by
  have ht : 504 < T := by linarith [Real.pi_gt_three]
  have harg := integral_sourceStripArgumentCorrection (by linarith : 0 < T)
  have hbottom := integral_sourceBottomLogWeight_original_budget hT
  have he : 681 / (2048 * T ^ 2) + 203 / (3072 * T ^ 2) =
      2449 / (6144 * T ^ 2) := by field_simp; norm_num
  have hfrac : (2449 : ℝ) / (6144 * T ^ 2) ≤ 2449 / (6144 * 504 ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith [sq_nonneg (T - 504)]
  have hlast : (2449 : ℝ) / (6144 * 504 ^ 2) + 1 / 1000000000 < 1 / 500000 := by norm_num
  linarith

#print axioms sourceHalfStripQuotient_right_boundary
#print axioms sourceHalfStripQuotient_bottom_boundary
#print axioms sourceHalfStripQuotient_linear_growth
#print axioms integral_sourceBottomLogWeight_original_budget
#print axioms sourceStrip_total_geometric_budget

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
