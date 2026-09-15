import LiuWang.Proof.Campaign20260915.ZetaWinding.DigammaEffective

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

theorem log_norm_sub_log_im_bounds {z : ℂ} (hy : 0 < z.im) :
    0 ≤ Real.log ‖z‖ - Real.log z.im ∧
      Real.log ‖z‖ - Real.log z.im ≤ z.re ^ 2 / (2 * z.im ^ 2) := by
  have hn : 0 < ‖z‖ := lt_of_lt_of_le hy (im_le_norm z)
  have hy2 : 0 < z.im ^ 2 := sq_pos_of_pos hy
  have hnorm : ‖z‖ ^ 2 = z.im ^ 2 * (1 + z.re ^ 2 / z.im ^ 2) := by
    rw [← normSq_eq_norm_sq]
    field_simp
    simp [normSq_apply]
    ring
  have hp : 0 < 1 + z.re ^ 2 / z.im ^ 2 := by positivity
  have hl := congrArg Real.log hnorm
  rw [Real.log_mul hy2.ne' hp.ne', Real.log_pow, Real.log_pow] at hl
  have hu := Real.log_le_sub_one_of_pos hp
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hy (im_le_norm z))
  · rw [mul_comm (2 : ℝ), div_mul_eq_div_div]
    norm_num at hl
    linarith

theorem digamma_re_log_im_error {z : ℂ} (ha : 0 < z.re) (hupper : z.re ≤ 9 / 4)
    (hy : 0 < z.im) :
    |(digamma z).re - Real.log z.im| ≤ 129 / (32 * z.im ^ 2) := by
  have hn : 0 < normSq z := normSq_pos.mpr (ne_zero_of_re_pos ha)
  have hy2 : 0 < z.im ^ 2 := sq_pos_of_pos hy
  have hsq : z.im ^ 2 ≤ normSq z := by
    simp only [normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hb := digamma_re_stirling_error ha
  have htail : 3 / (8 * normSq z) ≤ 3 / (8 * z.im ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hr : 0 ≤ (1 / z).re ∧ (1 / z).re ≤ z.re / z.im ^ 2 := by
    rw [one_div, inv_re]
    exact ⟨div_nonneg ha.le hn.le, div_le_div_of_nonneg_left ha.le hy2 hsq⟩
  have hl := log_norm_sub_log_im_bounds hy
  have herror : |(digamma z).re - Real.log z.im| ≤
      z.re ^ 2 / (2 * z.im ^ 2) + z.re / z.im ^ 2 / 2 + 3 / (8 * z.im ^ 2) := by
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2, hr.1, hr.2, hl.1, hl.2]
  refine herror.trans ?_
  have he : z.re ^ 2 / (2 * z.im ^ 2) + z.re / z.im ^ 2 / 2 + 3 / (8 * z.im ^ 2) =
      (4 * z.re ^ 2 + 4 * z.re + 3) / (8 * z.im ^ 2) := by
    field_simp
    ring
  rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
  have ha2 : z.re ^ 2 ≤ (9 / 4 : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 129 / 4 - (4 * z.re^2 + 4 * z.re + 3) by nlinarith) hy2.le]

theorem lehman_digamma_uniform_error {T x : ℝ} (hT : 0 < T)
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) (5 / 2)) :
    |(digamma (horizontalAt T x / 2 + 1)).re - Real.log (T / 2)| ≤
      129 / (8 * T ^ 2) := by
  have h := digamma_re_log_im_error (z := horizontalAt T x / 2 + 1)
    (by simp [horizontalAt]; linarith [hx.1])
    (by simp [horizontalAt]; linarith [hx.2])
    (by simp [horizontalAt]; linarith)
  have he : (horizontalAt T x / 2 + 1).im = T / 2 := by simp [horizontalAt]
  rw [he] at h
  convert! h using 1
  congr 1
  ring

theorem gamma_log_norm_horizontal_derivative {T x : ℝ} (hx : 1 / 2 ≤ x) :
    HasDerivAt (fun u => Real.log ‖Gamma (horizontalAt T u / 2 + 1)‖)
      ((digamma (horizontalAt T x / 2 + 1)).re / 2) x := by
  have hz : 0 < (horizontalAt T x / 2 + 1).re := by simp [horizontalAt]; linarith
  have hd : HasDerivAt (fun u => horizontalAt T u / 2 + 1) (1 / 2 : ℂ) x := by
    simpa [horizontalAt] using! (((ofRealCLM.hasDerivAt (x := x)).add_const
      ((T : ℂ) * I)).div_const 2).add_const 1
  have hg := (differentiableAt_Gamma _ (fun n => by
    intro he
    have hh := hz
    rw [he] at hh
    simp at hh
    linarith [Nat.cast_nonneg (α := ℝ) n])).hasDerivAt.scomp x hd
  have h := log_norm_hasDerivAt hg (Gamma_ne_zero_of_re_pos hz)
  convert! h using 1
  simp [digamma_def, logDeriv_apply, smul_eq_mul, div_eq_mul_inv, mul_re]
  ring

theorem lehmanGammaLog_pointwise_error {T x : ℝ} (hT : 0 < T)
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    |lehmanGammaLog T x + Real.log (T / 2) / 2| ≤ 129 / (16 * T ^ 2) := by
  let f : ℝ → ℝ := fun u => Real.log ‖Gamma (horizontalAt T u / 2 + 1)‖ -
    u * Real.log (T / 2) / 2
  let g : ℝ → ℝ := fun u => ((digamma (horizontalAt T u / 2 + 1)).re -
    Real.log (T / 2)) / 2
  have hd (u : ℝ) (hu : u ∈ Set.Icc x (x + 1)) : HasDerivAt f (g u) u := by
    have h := (gamma_log_norm_horizontal_derivative (T := T) (x := u)
      (by linarith [hx.1, hu.1])).sub
        (((hasDerivAt_id u).mul_const (Real.log (T / 2))).div_const 2)
    convert! h using 1
    dsimp [g]
    ring
  have hb (u : ℝ) (hu : u ∈ Set.Ico x (x + 1)) : ‖g u‖ ≤ 129 / (16 * T ^ 2) := by
    have h := lehman_digamma_uniform_error hT
      (x := u) ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hu.2]⟩
    simp only [g, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have he : 129 / (16 * T ^ 2) = (129 / (8 * T ^ 2)) / 2 := by
      rw [div_div]
      congr 1
      ring
    rw [he]
    exact div_le_div_of_nonneg_right h (by norm_num)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (hd u hu).hasDerivWithinAt) hb (x + 1) ⟨by linarith, le_rfl⟩
  have hg (u : ℝ) (hu : 1 / 2 ≤ u) : Gamma (horizontalAt T u / 2 + 1) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp [horizontalAt]; linarith)
  have he : lehmanGammaLog T x + Real.log (T / 2) / 2 = -(f (x + 1) - f x) := by
    rw [lehmanGammaLog, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hg x hx.1))
      (norm_ne_zero_iff.mpr (hg (x + 1) (by linarith [hx.1])))]
    dsimp [f]
    ring
  rw [he, abs_neg]
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, mul_one] using h

theorem lehmanGamma_integral_error {T : ℝ} (hT : 0 < T) :
    |(∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog T x) + Real.log (T / 2) / 2| ≤
      129 / (16 * T ^ 2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (f := fun x => lehmanGammaLog T x + Real.log (T / 2) / 2) (C := 129 / (16 * T ^ 2))
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact lehmanGammaLog_pointwise_error hT
        (Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) ▸ Set.uIoc_subset_uIcc hx))
  rw [intervalIntegral.integral_add (lehmanGammaLog_integrable T) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  norm_num at h
  exact h

theorem lehmanGamma_original_budget {T : ℝ} (hT : 168 * Real.pi < T) :
    |(∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog T x) + Real.log (T / 2) / 2| <
      9 / 100000 := by
  have ht : 504 < T := by linarith [Real.pi_gt_three]
  refine (lehmanGamma_integral_error (by linarith : 0 < T)).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg (T - 504)]

#print axioms digamma_re_log_im_error
#print axioms lehman_digamma_uniform_error
#print axioms lehmanGamma_integral_error
#print axioms lehmanGamma_original_budget

end LiuWang.Proof.Campaign20260915.ZetaWinding
