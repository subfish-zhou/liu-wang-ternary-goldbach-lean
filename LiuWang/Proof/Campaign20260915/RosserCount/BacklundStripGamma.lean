import LiuWang.Proof.Campaign20260915.RosserCount.BacklundStripBoundary

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.Campaign20260915.ZetaWinding

namespace LiuWang.Proof.Campaign20260915.RosserCount

theorem backlund_digamma_small_re_upper {z : ℂ} (hx : 0 < z.re)
    (hx' : z.re ≤ 1 / 2) (hy : 0 < z.im) :
    (digamma z).re ≤ Real.log z.im + 1 / (2 * z.im ^ 2) := by
  have hy2 : 0 < z.im ^ 2 := sq_pos_of_pos hy
  have hn : 0 < normSq z := normSq_pos.mpr (ne_zero_of_re_pos hx)
  have hsq : z.im ^ 2 ≤ normSq z := by
    simp only [normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hb := (abs_le.mp (digamma_re_stirling_error hx)).2
  have ht : 3 / (8 * normSq z) ≤ 3 / (8 * z.im ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hr : 0 ≤ (1 / z).re := by
    rw [one_div, inv_re]
    exact div_nonneg hx.le hn.le
  have hl := (log_norm_sub_log_im_bounds hy).2
  have hx2 : z.re ^ 2 / (2 * z.im ^ 2) ≤ 1 / (8 * z.im ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha : z.re ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hy2.le]
  have he : 1 / (8 * z.im ^ 2) + 3 / (8 * z.im ^ 2) =
      1 / (2 * z.im ^ 2) := by ring
  linarith

private theorem gamma_upper_log_derivative {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun u => Real.log ‖Gamma (horizontalAt y u)‖)
      (digamma (horizontalAt y x)).re x := by
  have hp : ∀ n : ℕ, horizontalAt y x ≠ -(n : ℂ) := by
    intro n he
    have h := congrArg Complex.im he
    simp [horizontalAt] at h
    linarith
  have hd : HasDerivAt (fun u => horizontalAt y u) (1 : ℂ) x := by
    simpa [horizontalAt] using ofRealCLM.hasDerivAt.add_const ((y : ℂ) * I)
  have hg := (differentiableAt_Gamma _ hp).hasDerivAt.scomp x hd
  simpa [digamma_def, logDeriv_apply, smul_eq_mul] using
    log_norm_hasDerivAt hg (Gamma_ne_zero hp)

theorem backlund_log_gamma_small_re_ratio {a b y : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hy : 0 < y) :
    Real.log ‖Gamma (horizontalAt y b)‖ - Real.log ‖Gamma (horizontalAt y a)‖ -
      (b - a) * Real.log y ≤ (b - a) / (2 * y ^ 2) := by
  let f : ℝ → ℝ := fun u => Real.log ‖Gamma (horizontalAt y u)‖ - u * Real.log y
  have hd (u : ℝ) : HasDerivAt f
      ((digamma (horizontalAt y u)).re - Real.log y) u := by
    simpa only [f, one_mul] using! (gamma_upper_log_derivative hy u).sub
      ((hasDerivAt_id u).mul_const (Real.log y))
  have hc : ContinuousOn f (Set.Icc a b) := fun u _ => (hd u).continuousAt.continuousWithinAt
  have hd' : DifferentiableOn ℝ f (interior (Set.Icc a b)) :=
    fun u _ => (hd u).differentiableAt.differentiableWithinAt
  have hbound (u : ℝ) (hu : u ∈ interior (Set.Icc a b)) :
      deriv f u ≤ 1 / (2 * y ^ 2) := by
    rw [interior_Icc] at hu
    rw [(hd u).deriv]
    have h := backlund_digamma_small_re_upper (z := horizontalAt y u)
      (by simp [horizontalAt]; linarith [hu.1])
      (by simp [horizontalAt]; linarith [hu.2])
      (by simpa [horizontalAt] using hy)
    simpa only [horizontalAt, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero, sub_le_iff_le_add, add_comm] using h
  have h := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hd' hbound
    a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  dsimp [f] at h
  convert! h using 1 <;> ring

theorem backlund_gamma_small_re_ratio_le {a b y : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hy : 0 < y) :
    ‖Gamma (horizontalAt y b)‖ ≤
      ‖Gamma (horizontalAt y a)‖ * y ^ (b - a) *
        Real.exp ((b - a) / (2 * y ^ 2)) := by
  have hp (x : ℝ) : 0 < ‖Gamma (horizontalAt y x)‖ := by
    apply norm_pos_iff.mpr
    apply Gamma_ne_zero
    intro n he
    have h := congrArg Complex.im he
    simp [horizontalAt] at h
    linarith
  have h := backlund_log_gamma_small_re_ratio ha hab hb hy
  calc
    _ = Real.exp (Real.log ‖Gamma (horizontalAt y b)‖) := (Real.exp_log (hp b)).symm
    _ ≤ Real.exp (Real.log ‖Gamma (horizontalAt y a)‖ +
        (b - a) * Real.log y + (b - a) / (2 * y ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (hp a), Real.rpow_def_of_pos hy]
      rw [mul_comm (b - a) (Real.log y)]

theorem backlund_gamma_strip_reference {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (ht : 0 < s.im) :
    ‖Gamma (horizontalAt (s.im / 2) (1 / 2))‖ ≤
      ‖Gamma (s / 2)‖ * (s.im / 2) ^ ((1 - s.re) / 2) *
        Real.exp (1 / s.im ^ 2) := by
  have h := backlund_gamma_small_re_ratio_le (a := s.re / 2) (b := 1 / 2)
    (y := s.im / 2) (by positivity) (by linarith) le_rfl (by positivity)
  have he : horizontalAt (s.im / 2) (s.re / 2) = s / 2 := by
    apply Complex.ext <;> simp [horizontalAt]
  rw [he, show (1 / 2 : ℝ) - s.re / 2 = (1 - s.re) / 2 by ring] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  have he' : ((1 - s.re) / 2) / (2 * (s.im / 2) ^ 2) =
      (1 - s.re) / s.im ^ 2 := by ring
  rw [he']
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

#print axioms backlund_digamma_small_re_upper
#print axioms backlund_log_gamma_small_re_ratio
#print axioms backlund_gamma_small_re_ratio_le
#print axioms backlund_gamma_strip_reference

end LiuWang.Proof.Campaign20260915.RosserCount
