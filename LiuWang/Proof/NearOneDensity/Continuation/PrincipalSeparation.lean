import LiuWang.Proof.NearOneDensity.Continuation.ShiftedCost

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity.Continuation

theorem small_sigma_tau_bounds {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    3 / 5 ≤ stechkinSigma σ - 1 ∧ stechkinSigma σ - 1 ≤ 633 / 1000 := by
  have hτ := stechkinSigma_bounds hσ (by linarith)
  have he := stechkinSigma_equation σ
  have hg := stechkinSigma_ge hσ
  constructor
  · linarith [hτ.1]
  · have hsquare : σ ^ 2 ≤ (203 / 200 : ℝ) ^ 2 := by nlinarith
    nlinarith

theorem poleDifference_real_kernel {σ t : ℝ} :
    poleDifference σ t = (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) -
      stechkinK * ((stechkinSigma σ - 1) / ((stechkinSigma σ - 1) ^ 2 + t ^ 2)) := by
  simp only [poleDifference, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add]
  simp only [sq]

theorem poleDifference_small_sigma_nonpos {σ t : ℝ} (hσ : 1 < σ)
    (hσ₁ : σ ≤ 203 / 200) (ht : 1 / 4 ≤ |t|) : poleDifference σ t ≤ 0 := by
  have hv := small_sigma_tau_bounds hσ hσ₁
  have hkv : 1341 / 5000 ≤ stechkinK * (stechkinSigma σ - 1) := by
    have hh := mul_le_mul stechkinK_ge_447 hv.1 (by norm_num) stechkinK_mem.1
    norm_num at hh
    exact hh
  have ht2 : 1 / 16 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hv2 : (stechkinSigma σ - 1) ^ 2 ≤ (633 / 1000 : ℝ) ^ 2 := by nlinarith [hv.1, hv.2]
  have hu : 0 < σ - 1 := by linarith
  have hv0 : 0 < stechkinSigma σ - 1 := by linarith [hv.1]
  have hprod := mul_le_mul (show σ - 1 ≤ 3 / 200 by linarith) hv2
    (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 200)
  have hY := mul_le_mul_of_nonneg_right (show σ - 1 ≤ 3 / 200 by linarith) (sq_nonneg t)
  have hbig := mul_le_mul_of_nonneg_right hkv (sq_nonneg t)
  have hpos : 0 ≤ stechkinK * (stechkinSigma σ - 1) * (σ - 1) ^ 2 := by positivity
  rw [poleDifference_real_kernel]
  apply sub_nonpos.mpr
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem damped_pole_low_saving {σ t : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200)
    (ht : |t| ≤ 1 / 4) :
    57 / 100 ≤ stechkinK * ((stechkinSigma σ - 1) /
      ((stechkinSigma σ - 1) ^ 2 + t ^ 2)) := by
  have hv := small_sigma_tau_bounds hσ hσ₁
  have hv0 : 0 < stechkinSigma σ - 1 := by linarith [hv.1]
  have hv2 : (stechkinSigma σ - 1) ^ 2 ≤ (633 / 1000 : ℝ) ^ 2 := by nlinarith [hv.1, hv.2]
  have ht2 : t ^ 2 ≤ 1 / 16 := by
    have hh := mul_le_mul ht ht (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith [sq_abs t]
  have hkv := mul_le_mul stechkinK_ge_447 hv.1 (by norm_num) stechkinK_mem.1
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem row_pole_shape (r : DensityRow) :
    rowA r / (rowA r ^ 2 + 4 * rowRadius r ^ 2) ≤ 7 / 40 := by
  cases r <;> norm_num [rowA, rowRadius]

theorem row_separated_pole {z t : ℝ} (r : DensityRow) (hz : 100000000000 ≤ z)
    (ht : 2 * (rowRadius r / Real.log z) ≤ |t|) :
    (rowA r / Real.log z) / ((rowA r / Real.log z) ^ 2 + t ^ 2) ≤
      (7 / 40) * Real.log z := by
  have ha := (row_basic_certificate r).1
  have hL : 0 < Real.log z := by linarith [source_log_lower hz]
  have hpos : 0 < rowA r / Real.log z := div_pos ha hL
  have hrad : 0 ≤ 2 * (rowRadius r / Real.log z) := by
    exact mul_nonneg (by norm_num) (div_nonneg (rowRadius_nonneg r) hL.le)
  have ht2 : (2 * (rowRadius r / Real.log z)) ^ 2 ≤ t ^ 2 := by
    have hh := mul_le_mul ht ht hrad (abs_nonneg t)
    nlinarith [sq_abs t]
  have hh := div_le_div_of_nonneg_left hpos.le
    (show 0 < (rowA r / Real.log z) ^ 2 + (2 * (rowRadius r / Real.log z)) ^ 2 by positivity)
    (show (rowA r / Real.log z) ^ 2 + (2 * (rowRadius r / Real.log z)) ^ 2 ≤
      (rowA r / Real.log z) ^ 2 + t ^ 2 by linarith)
  have he : (rowA r / Real.log z) /
      ((rowA r / Real.log z) ^ 2 + (2 * (rowRadius r / Real.log z)) ^ 2) =
      Real.log z * (rowA r / (rowA r ^ 2 + 4 * rowRadius r ^ 2)) := by
    field_simp
    ring
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_left (row_pole_shape r) hL.le
  nlinarith

theorem principal_row_separated_cost (r : DensityRow) {q : ℕ} [NeZero q] {z t : ℝ}
    (hz : 100000000000 ≤ z) (hlevel : Real.log q ≤ Real.log z)
    (hheight : Real.log q + Real.log (max 1 |t|) ≤ Real.log z + Real.log 2)
    (hsep : 2 * (rowRadius r / Real.log z) ≤ |t|) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK (1 : DirichletCharacter ℂ q) t ≤
      Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z) := by
  dsimp only
  rw [logKernel_eq_dampedLogDeriv]
  have hσ := row_sigma_bounds r hz
  have hL : 0 < Real.log z := by linarith [source_log_lower hz]
  have he : Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z) =
      stechkinConductorCoeff * Real.log z + 0.7647 := by
    unfold crossBudget
    field_simp
  rw [he]
  have heuler := principal_damped_euler_bound (q := q) hσ.1 t
  change dampedLogDeriv (1 : DirichletCharacter ℂ q) _ _ _ t ≤
    zetaDamped (1 + rowA r / Real.log z) t + principalPrimeCost q _ at heuler
  have hzeta := zeta_damped_pole_bound hσ.1 t
  change zetaDamped (1 + rowA r / Real.log z) t ≤ _ at hzeta
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  by_cases htlow : |t| ≤ 1 / 4
  · have hg := shiftedGamma_small_sigma hσ.1 hσ.2 t
    rw [max_eq_left (by linarith : |t| ≤ 1), Real.log_one, mul_zero, zero_add] at hg
    have hc := principalPrimeCost_tenth q hσ.1 hσ.2
    have hp := row_separated_pole r hz hsep
    have hs := damped_pole_low_saving hσ.1 hσ.2 htlow
    have hpol : poleDifference (1 + rowA r / Real.log z) t ≤ (7 / 40) * Real.log z - 57 / 100 := by
      rw [poleDifference_real_kernel]
      simp only [add_sub_cancel_left]
      linarith
    have hkl := mul_le_mul_of_nonneg_right hk hL.le
    nlinarith
  have hpol := poleDifference_small_sigma_nonpos hσ.1 hσ.2 (le_of_not_ge htlow)
  have hc := principalPrimeCost_kappa q hσ.1 hσ.2
  by_cases htone : |t| ≤ 1
  · have hg := shiftedGamma_small_sigma hσ.1 hσ.2 t
    rw [max_eq_left htone, Real.log_one, mul_zero, zero_add] at hg
    have hlev := mul_le_mul_of_nonneg_left hlevel (by linarith : 0 ≤ stechkinConductorCoeff)
    linarith
  · have hg := shiftedGamma_row_function hσ.1 hσ.2 t
    have hh := mul_le_mul_of_nonneg_left hheight (by linarith : 0 ≤ stechkinConductorCoeff)
    nlinarith [principal_high_constant]

end LiuWang.Proof.NearOneDensity.Continuation
