import LiuWang.Proof.ChebyshevBound.IntegratedFormula.MellinSum

/-! # 全体实际带重数零点的 Mellin 恒等式，含绝对可积交换。 -/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

instance : Countable RiemannXiDivisorZeroIndex := by
  have h := xi_height_inverse_square_summable.countable_support
  have hs : Function.support
      (fun p : RiemannXiDivisorZeroIndex => 1 / (riemannXiDivisorZeroValue p).im ^ 2) = univ := by
    ext p
    have ht : (riemannXiDivisorZeroValue p).im ≠ 0 := by
      intro he
      have h := xi_zero_height_gt_one p
      norm_num [he] at h
    simp [Function.mem_support, ht]
  rw [hs] at h
  exact Set.countable_univ_iff.mp h

theorem zeroMellinTerm_norm_le (p : RiemannXiDivisorZeroIndex) {u : ℝ} (hu : 0 < u) :
    ‖zeroMellinTerm p u‖ ≤
      (2 * (1 / (riemannXiDivisorZeroValue p).im ^ 2)) * ‖powerCut (-1) u‖ := by
  by_cases hu1 : u ≤ 1
  · have hmem : u ∈ Ioc 0 1 := ⟨hu, hu1⟩
    let ρ := riemannXiDivisorZeroValue p
    have hr := riemannXiDivisorZeroValue_re_mem_Ioo p
    have ht : 0 < ρ.im ^ 2 := by
      have h := xi_zero_height_gt_one p
      have : 0 < |ρ.im| := by dsimp [ρ]; linarith
      exact sq_pos_of_ne_zero (abs_pos.mp this)
    have hden : ρ.im ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
      have h1 := Complex.abs_im_le_norm ρ
      have h2 := Complex.abs_im_le_norm (ρ + 1)
      simp only [Complex.add_im, Complex.one_im, add_zero] at h2
      simpa only [← sq, sq_abs] using mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    have hp : ‖(u : ℂ) ^ (-ρ)‖ ≤ u⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re]
      have h := Real.rpow_le_rpow_of_exponent_ge hu hu1
        (by dsimp [ρ]; linarith [hr.2] : (-1 : ℝ) ≤ -ρ.re)
      simpa only [Real.rpow_neg_one] using h
    have hui : u ≤ u⁻¹ := by
      have : 1 ≤ u⁻¹ := (one_le_inv₀ hu).2 hu1
      linarith
    have hnum : ‖(u : ℂ) ^ (-ρ) - (u : ℂ)‖ ≤ 2 * u⁻¹ := by
      have h := norm_sub_le ((u : ℂ) ^ (-ρ)) (u : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] at h
      linarith
    have hpow : ‖powerCut (-1) u‖ = u⁻¹ := by
      simp [powerCut, hmem, Complex.norm_cpow_eq_rpow_re_of_pos hu, Real.rpow_neg_one]
    rw [hpow]
    change ‖(powerCut (-ρ) u - powerCut 1 u) / (ρ * (ρ + 1))‖ ≤
      (2 * (1 / ρ.im ^ 2)) * u⁻¹
    simp only [powerCut, indicator_of_mem hmem, Complex.cpow_one, norm_div, norm_mul]
    calc
      _ ≤ (2 * u⁻¹) / (‖ρ‖ * ‖ρ + 1‖) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * u⁻¹) / ρ.im ^ 2 := div_le_div_of_nonneg_left (by positivity) ht hden
      _ = _ := by ring
  · have hn : u ∉ Ioc 0 1 := fun h => hu1 h.2
    simp [zeroMellinTerm, powerCut, hn]

theorem zeroMellinTerm_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun p => zeroMellinTerm p u) :=
  ((xi_height_inverse_square_summable.mul_left 2).mul_right ‖powerCut (-1) u‖).of_norm_bounded
    (fun p => zeroMellinTerm_norm_le p hu)

theorem hasMellin_zeroSum {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u => ∑' p, zeroMellinTerm p u) s
      ((∑' p, xiTerm s p) / (s * (s + 1))) := by
  have h := hasMellin_tsum_dominated (fun p => hasMellin_zeroMellinTerm p hs)
    (hasMellin_powerCut (-1) (s := s) (by simp; linarith)).1
    (xi_height_inverse_square_summable.mul_left 2)
    (fun p _ hu => zeroMellinTerm_norm_le p hu)
  simpa only [tsum_div_const] using h

theorem zeroSum_at_inverse {x : ℝ} (hx : 1 ≤ x) :
    (x : ℂ) * (∑' p, zeroMellinTerm p x⁻¹) =
      ∑' p, (integratedZeroTerm x p - integratedZeroTerm 1 p) := by
  have hx0 : 0 < x := by linarith
  simp_rw [zeroMellinTerm_at_inverse hx]
  rw [tsum_div_const, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hx0.ne')]

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
