import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripFactorBudget

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

private theorem arctan_abs_nonneg_bound {x : ℝ} (hx : 0 ≤ x) :
    |Real.arctan x| ≤ x := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := x)
    (fun u _ => (Real.hasDerivAt_arctan u).hasDerivWithinAt)
    (C := 1) (fun u _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity : 0 < 1 + u ^ 2)).mpr (by nlinarith [sq_nonneg u]))
    x ⟨hx, le_rfl⟩
  simpa only [Real.arctan_zero, sub_zero, Real.norm_eq_abs, one_mul] using h

theorem backlund_log_norm_budget {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1000 ≤ s.im) :
    ‖Complex.log (-s * I)‖ ≤ Real.log s.im * (1 + 1 / s.im ^ 2) := by
  have ht0 : 0 < s.im := by linarith
  have hl1 : 1 ≤ Real.log s.im := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : 3 ≤ s.im)
    linarith [Real.log_three_gt_d9]
  have hl := log_norm_sub_log_im_bounds ht0
  have hσ : s.re ^ 2 ≤ 1 := by nlinarith
  have hreal : (Complex.log (-s * I)).re = Real.log ‖s‖ := by
    rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one]
  have himag : (Complex.log (-s * I)).im = -Real.arctan (s.re / s.im) := by
    rw [LiuWang.Proof.Campaign20260915.ZetaValidation.log_im_of_re_pos
      (by simpa using ht0)]
    simp only [mul_im, neg_re, neg_im, I_im, I_re, mul_one, mul_zero, add_zero,
      mul_re, zero_sub, neg_neg, neg_div, Real.arctan_neg]
  have hi : |(Complex.log (-s * I)).im| ≤ 1 / s.im := by
    rw [himag, abs_neg]
    exact (arctan_abs_nonneg_bound (div_nonneg hs ht0.le)).trans
      (div_le_div_of_nonneg_right hs' ht0.le)
  have hisq : (Complex.log (-s * I)).im ^ 2 ≤ 1 / s.im ^ 2 := by
    calc
      _ = |(Complex.log (-s * I)).im| ^ 2 := (sq_abs _).symm
      _ ≤ (1 / s.im) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
      _ = _ := by ring
  have hlu : Real.log ‖s‖ ≤ Real.log s.im + (1 / s.im ^ 2) / 2 := by
    have h := hl.2.trans (div_le_div_of_nonneg_right hσ (by positivity))
    have he : 1 / (2 * s.im ^ 2) = (1 / s.im ^ 2) / 2 := by ring
    rw [he] at h
    linarith
  have hl0 : 0 ≤ Real.log ‖s‖ := by linarith [hl.1]
  have hlu0 : 0 ≤ Real.log s.im + (1 / s.im ^ 2) / 2 := by positivity
  have hlsq := pow_le_pow_left₀ hl0 hlu 2
  have hu : 0 ≤ 1 / s.im ^ 2 := by positivity
  have hscalar : (Real.log s.im + (1 / s.im ^ 2) / 2) ^ 2 + 1 / s.im ^ 2 ≤
      (Real.log s.im * (1 + 1 / s.im ^ 2)) ^ 2 := by
    have ha : 0 ≤ 2 * (Real.log s.im) ^ 2 - Real.log s.im - 1 := by nlinarith
    have hb : 0 ≤ (Real.log s.im) ^ 2 - 1 / 4 := by nlinarith
    nlinarith [mul_nonneg ha hu, mul_nonneg hb (sq_nonneg (1 / s.im ^ 2))]
  have hnorm := Complex.sq_norm (Complex.log (-s * I))
  rw [normSq_apply, hreal] at hnorm
  have hr : 0 ≤ Real.log s.im * (1 + 1 / s.im ^ 2) := by positivity
  nlinarith [norm_nonneg (Complex.log (-s * I))]

theorem backlund_strip_scalar_budget {t : ℝ} (ht : 1000 ≤ t) :
    Real.exp (3 / (2 * t ^ 2)) * (1 + 1 / t ^ 2) ≤ t ^ 2 / (t ^ 2 - 4) := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have hd' : 0 < 2 * t ^ 2 - 3 := by nlinarith
  have hc : 3 / (2 * t ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  calc
    _ ≤ 1 / (1 - 3 / (2 * t ^ 2)) * (1 + 1 / t ^ 2) :=
      mul_le_mul_of_nonneg_right
        (Real.exp_bound_div_one_sub_of_interval (by positivity) hc) (by positivity)
    _ = 2 * (t ^ 2 + 1) / (2 * t ^ 2 - 3) := by
      field_simp
    _ ≤ _ := by
      rw [div_le_div_iff₀ hd' hd]
      nlinarith [sq_nonneg t]

theorem backlund_zeta_le_original_Phi_bound {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 1000 ≤ s.im) :
    ‖riemannZeta s‖ ≤ ‖backlundStripPhi s‖ * (s.im ^ 2 / (s.im ^ 2 - 4)) *
      (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.log s.im := by
  have ht0 : 0 < s.im := by linarith
  have hl0 : 0 ≤ Real.log s.im := Real.log_nonneg (by linarith)
  calc
    _ ≤ ‖backlundStripPhi s‖ * ‖Complex.log (-s * I)‖ *
        (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.exp (3 / (2 * s.im ^ 2)) :=
      backlund_zeta_le_original_Phi_profile hs hs' (by linarith)
    _ ≤ ‖backlundStripPhi s‖ * (Real.log s.im * (1 + 1 / s.im ^ 2)) *
        (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) * Real.exp (3 / (2 * s.im ^ 2)) := by
      gcongr
      exact backlund_log_norm_budget hs hs' ht
    _ = (‖backlundStripPhi s‖ * (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) *
        Real.log s.im) * (Real.exp (3 / (2 * s.im ^ 2)) * (1 + 1 / s.im ^ 2)) := by ring
    _ ≤ (‖backlundStripPhi s‖ * (s.im / (2 * Real.pi)) ^ ((1 - s.re) / 2) *
        Real.log s.im) * (s.im ^ 2 / (s.im ^ 2 - 4)) :=
      mul_le_mul_of_nonneg_left (backlund_strip_scalar_budget ht) (by positivity)
    _ = _ := by ring

#print axioms backlund_log_norm_budget
#print axioms backlund_strip_scalar_budget
#print axioms backlund_zeta_le_original_Phi_bound

end LiuWang.Proof.Campaign20260915.RosserCount
