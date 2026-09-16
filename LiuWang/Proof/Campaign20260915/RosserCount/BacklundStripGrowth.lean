import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripLogBudget

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem exists_completed_zeta_uniform_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 1 ≤ |s.im| →
      ‖completedRiemannZeta s‖ ≤ C := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  let w (a : ℂ) (x : ℝ) := ‖(x : ℂ) ^ (a - 1) • P.f_modif x‖
  have hi (a : ℂ) : IntegrableOn (w a) (Ioi 0) :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin a).1.norm
  let C := ∫ x in Ioi (0 : ℝ), w 0 x + w (1 / 2) x
  have hC : 0 ≤ C := integral_nonneg (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hm {z : ℂ} (hz : 0 ≤ z.re) (hz' : z.re ≤ 1 / 2) :
      ‖P.Λ₀ z‖ ≤ C := by
    apply norm_integral_le_of_norm_le ((hi 0).add (hi (1 / 2)))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have he (a : ℂ) :
        w a x = x ^ (a.re - 1) * ‖P.f_modif x‖ := by
      change ‖(x : ℂ) ^ (a - 1) • P.f_modif x‖ = _
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    change w z x ≤ w 0 x + w (1 / 2) x
    rw [he, he, he]
    norm_num only [zero_re, div_ofNat_re, one_re, zero_sub]
    by_cases hx1 : 1 ≤ x
    · have hb := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : z.re - 1 ≤ 1 / 2 - 1))
        (norm_nonneg (P.f_modif x))
      linarith [mul_nonneg (Real.rpow_nonneg hx.le (-1)) (norm_nonneg (P.f_modif x))]
    · have hb := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1)
          (by linarith : (-1 : ℝ) ≤ z.re - 1)) (norm_nonneg (P.f_modif x))
      linarith [mul_nonneg (Real.rpow_nonneg hx.le (1 / 2 - 1)) (norm_nonneg (P.f_modif x))]
  refine ⟨C + 3, by linarith, ?_⟩
  intro s hs hs' ht
  have hzero : ‖completedRiemannZeta₀ s‖ ≤ C / 2 := by
    change ‖P.Λ₀ (s / 2) / 2‖ ≤ _
    rw [norm_div]
    norm_num only [norm_ofNat]
    exact div_le_div_of_nonneg_right (hm (by simp; linarith) (by simp; linarith))
      (by norm_num)
  have hnorm : 1 ≤ ‖s‖ := ht.trans (abs_im_le_norm s)
  have hnorm' : 1 ≤ ‖1 - s‖ := by
    have h := abs_im_le_norm (1 - s)
    simp only [sub_im, one_im, zero_sub, abs_neg] at h
    exact ht.trans h
  have h1 : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hnorm
  have h2 : ‖1 / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hnorm'
  rw [completedRiemannZeta_eq]
  have ha := norm_sub_le (completedRiemannZeta₀ s - 1 / s) (1 / (1 - s))
  have hb := norm_sub_le (completedRiemannZeta₀ s) (1 / s)
  linarith

theorem backlundStripPhi_completed {s : ℂ} (ht : 1 < s.im) :
    backlundStripPhi s =
      completedRiemannZeta s * Complex.sqrt (Complex.sin ((Real.pi : ℂ) * s / 2)) /
        Complex.log (-s * I) := by
  have hs0 : s ≠ 0 := by intro he; rw [he] at ht; norm_num at ht
  have hg : Gamma (s / 2) ≠ 0 := by
    apply Gamma_ne_zero
    intro n he
    have h := congrArg Complex.im he
    simp only [div_ofNat_im, neg_im, natCast_im] at h
    linarith
  have hp : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  rw [backlundStripPhi, backlundStripFactor, riemannZeta_def_of_ne_zero hs0,
    Complex.Gammaℝ_def]
  field_simp

private theorem norm_sine_le_exp_im {z : ℂ} (hz : 0 ≤ z.im) :
    ‖Complex.sin z‖ ≤ Real.exp z.im := by
  have h := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  simp only [Complex.norm_exp, mul_re, neg_re, neg_im, I_re, I_im, mul_zero,
    mul_one, zero_sub, neg_neg] at h
  have he : Real.exp (-z.im) ≤ Real.exp z.im := Real.exp_le_exp.mpr (by linarith)
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one]
  norm_num only [norm_ofNat]
  linarith

theorem exists_backlundStripPhi_exponential_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 1000 ≤ s.im →
      ‖backlundStripPhi s‖ ≤ C * Real.exp (Real.pi * s.im / 2) := by
  obtain ⟨C, hC, hc⟩ := exists_completed_zeta_uniform_strip_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs' ht
  have ht0 : 0 < s.im := by linarith
  have hb := hc s hs hs' (by rw [abs_of_pos ht0]; linarith)
  let z := (Real.pi : ℂ) * s / 2
  have hz : z.im = Real.pi * s.im / 2 := by simp [z]
  have hz0 : 0 ≤ z.im := by rw [hz]; positivity
  have hn := norm_sine_le_exp_im hz0
  have hsq : ‖Complex.sqrt (Complex.sin z)‖ ^ 2 = ‖Complex.sin z‖ := by
    rw [Complex.sqrt, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, Real.sq_sqrt (norm_nonneg _)]
  have hroot : ‖Complex.sqrt (Complex.sin z)‖ ≤ Real.exp z.im := by
    have he := Real.one_le_exp_iff.mpr hz0
    nlinarith [norm_nonneg (Complex.sqrt (Complex.sin z)), Real.exp_pos z.im]
  have hl : 1 ≤ ‖Complex.log (-s * I)‖ := by
    have hl3 := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : 3 ≤ s.im)
    have hln := Real.log_le_log ht0 (im_le_norm s)
    have hr := re_le_norm (Complex.log (-s * I))
    rw [Complex.log_re, norm_mul, norm_neg, norm_I, mul_one] at hr
    linarith [Real.log_three_gt_d9]
  rw [backlundStripPhi_completed (by linarith), norm_div, norm_mul]
  calc
    _ ≤ ‖completedRiemannZeta s‖ * ‖Complex.sqrt (Complex.sin z)‖ :=
      div_le_self (by positivity) hl
    _ ≤ C * Real.exp z.im := mul_le_mul hb hroot (norm_nonneg _) hC.le
    _ = _ := by rw [hz]

#print axioms exists_completed_zeta_uniform_strip_bound
#print axioms backlundStripPhi_completed
#print axioms exists_backlundStripPhi_exponential_growth

end LiuWang.Proof.Campaign20260915.RosserCount
