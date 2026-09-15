import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Inversion

/-! # 实际积分 psi 的两端点显式公式及全 Γ 修正范数界。 -/

set_option autoImplicit false
noncomputable section

open Complex Set
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

def gammaCorrection (x : ℝ) : ℂ := (x : ℂ) * ∑' n, gammaMellinTerm n x⁻¹

theorem gamma_weights_sum_le_two :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  have ht := Complex.tsum_one_div_natCast_add_add_one_sq_le (N := 1) le_rfl
  have hs := gammaMellin_weights_summable.sum_add_tsum_nat_add 1
  norm_num [Finset.sum_range_succ] at hs ht
  simp only [one_div]
  linarith

theorem gammaCorrection_norm_le {x : ℝ} (hx : 1 ≤ x) : ‖gammaCorrection x‖ ≤ 2 * x := by
  have hx0 : 0 < x := by linarith
  have hu0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hu1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hs := (gammaMellinTerm_summable hu0).norm.tsum_le_tsum
    (fun n => gammaMellinTerm_norm_le n hu0)
    (gammaMellin_weights_summable.mul_right ‖powerCut 0 x⁻¹‖)
  have hpow : ‖powerCut 0 x⁻¹‖ = 1 := by simp [powerCut, hu0, hu1]
  simp only [hpow, mul_one] at hs
  have hn := (norm_tsum_le_tsum_norm (gammaMellinTerm_summable hu0).norm).trans
    (hs.trans gamma_weights_sum_le_two)
  rw [gammaCorrection, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  nlinarith

theorem integratedZeroTerm_summable_one :
    Summable (integratedZeroTerm 1) := by
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ xi_height_inverse_square_summable
  intro p
  have h := integratedZeroTerm_norm_le (x := 1) (by norm_num) p
  simpa [xiZeroWeight] using h

theorem scaled_triangle_inverse {x : ℝ} (hx : 1 ≤ x) :
    (x : ℂ) * triangle x⁻¹ = (x : ℂ) - 1 := by
  have hx0 : 0 < x := by linarith
  rw [triangle_of_pos (inv_pos.mpr hx0),
    max_eq_right (sub_nonneg.mpr (inv_le_one_of_one_le₀ hx))]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hx0.ne']

theorem scaled_pole_inverse {x : ℝ} (hx : 1 ≤ x) :
    (x : ℂ) * poleMellin x⁻¹ = ((x : ℂ) - 1) ^ 2 / 2 := by
  have hx0 : 0 < x := by linarith
  have hu : x⁻¹ ∈ Ioc 0 1 := ⟨inv_pos.mpr hx0, inv_le_one_of_one_le₀ hx⟩
  simp only [poleMellin, powerCut, indicator_of_mem hu, Complex.cpow_neg_one,
    Complex.cpow_zero, mul_one, Complex.cpow_one, Complex.ofReal_inv, inv_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx0.ne']
  ring

theorem integratedPsi_formula {x : ℝ} (hx : 1 < x) (hlog : 3100 ≤ Real.log x) :
    (integratedPsi x : ℂ) =
      ((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) * ((x : ℂ) - 1) +
      ((x : ℂ) - 1) ^ 2 / 2 -
      ((∑' p, integratedZeroTerm x p) - ∑' p, integratedZeroTerm 1 p) +
      gammaCorrection x := by
  rw [integratedPsi_eq_spectral hx]
  unfold spectralMellin
  rw [mul_add, mul_add, mul_sub, mul_left_comm _ _ (triangle x⁻¹),
    scaled_triangle_inverse hx.le, scaled_pole_inverse hx.le, zeroSum_at_inverse hx.le,
    (integratedZeroTerm_summable (by linarith) hlog).tsum_sub integratedZeroTerm_summable_one]
  unfold gammaCorrection
  ring

theorem integratedPsi_difference_formula {x y : ℝ}
    (hx : 1 < x) (hy : 1 < y) (hlogx : 3100 ≤ Real.log x) (hlogy : 3100 ≤ Real.log y) :
    ((integratedPsi y - integratedPsi x : ℝ) : ℂ) =
      (((y ^ 2 - x ^ 2) / 2 - Real.log (2 * Real.pi) * (y - x) : ℝ) : ℂ) -
      ((∑' p, integratedZeroTerm y p) - ∑' p, integratedZeroTerm x p) +
      (gammaCorrection y - gammaCorrection x) := by
  rw [Complex.ofReal_sub, integratedPsi_formula hy hlogy, integratedPsi_formula hx hlogx]
  push_cast
  ring

theorem integratedPsi_difference_upper {x y : ℝ}
    (hx : 1 < x) (hxy : x ≤ y) (hlogx : 3100 ≤ Real.log x) :
    integratedPsi y - integratedPsi x ≤
      (y ^ 2 - x ^ 2) / 2 +
      ‖(∑' p, integratedZeroTerm y p) - ∑' p, integratedZeroTerm x p‖ + 2 * (y + x) := by
  have hy : 1 < y := hx.trans_le hxy
  have hlogy := hlogx.trans (Real.log_le_log (by linarith) hxy)
  have hid := congrArg Complex.re (integratedPsi_difference_formula hx hy hlogx hlogy)
  simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re] at hid
  have hz := Complex.re_le_norm
    (-((∑' p, integratedZeroTerm y p) - ∑' p, integratedZeroTerm x p))
  simp only [Complex.neg_re, Complex.sub_re, norm_neg] at hz
  have hg := (Complex.re_le_norm (gammaCorrection y - gammaCorrection x)).trans
    ((norm_sub_le _ _).trans (add_le_add (gammaCorrection_norm_le hy.le)
      (gammaCorrection_norm_le hx.le)))
  simp only [Complex.sub_re] at hg
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hc := mul_nonneg hlog (sub_nonneg.mpr hxy)
  linarith

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
