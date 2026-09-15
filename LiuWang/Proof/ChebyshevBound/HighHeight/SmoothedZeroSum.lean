import LiuWang.Proof.ChebyshevBound.HighHeight.ZeroContribution

/-!
# 二次平滑显式公式中实际复零点和的原阈值界

分母为 ρ(ρ+1)，分子为 x^(ρ+1)，使用全部实际 ξ 零点及其解析重数。
尚须另证此零点和与积分 Chebyshev 函数之间的完整显式公式。
-/

set_option autoImplicit false
noncomputable section

open Complex BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ChebyshevBound.HighHeight

def integratedZeroTerm (x : ℝ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  (x : ℂ) ^ (riemannXiDivisorZeroValue p + 1) /
    (riemannXiDivisorZeroValue p * (riemannXiDivisorZeroValue p + 1))

theorem integratedZeroTerm_norm_le {x : ℝ} (hx : 0 < x)
    (p : RiemannXiDivisorZeroIndex) :
    ‖integratedZeroTerm x p‖ ≤ x ^ 2 * xiZeroWeight x p := by
  let ρ := riemannXiDivisorZeroValue p
  have hden : ρ.im ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
    have h1 := Complex.abs_im_le_norm ρ
    have h2 := Complex.abs_im_le_norm (ρ + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero] at h2
    simpa only [← sq, sq_abs] using mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  have ht := xi_zero_height_gt_one p
  have ht2 : 0 < ρ.im ^ 2 := by
    have : 0 < |ρ.im| := by dsimp [ρ]; linarith
    exact sq_pos_of_ne_zero (abs_pos.mp this)
  have hpow : ‖(x : ℂ) ^ (ρ + 1)‖ =
      x ^ 2 * Real.exp ((ρ.re - 1) * Real.log x) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_def_of_pos hx]
    simp only [Complex.add_re, Complex.one_re]
    rw [show Real.log x * (ρ.re + 1) = 2 * Real.log x + (ρ.re - 1) * Real.log x by ring,
      Real.exp_add, show Real.exp (2 * Real.log x) = x ^ 2 by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hx]]
  change ‖(x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖ ≤
    x ^ 2 * (Real.exp ((ρ.re - 1) * Real.log x) / ρ.im ^ 2)
  rw [norm_div, norm_mul, hpow]
  calc
    _ ≤ (x ^ 2 * Real.exp ((ρ.re - 1) * Real.log x)) / ρ.im ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) ht2 hden
    _ = _ := by ring

theorem integratedZeroTerm_summable {x : ℝ} (hx : 0 < x) (hlog : 3100 ≤ Real.log x) :
    Summable (integratedZeroTerm x) := by
  apply summable_norm_iff.mp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (integratedZeroTerm_norm_le hx)
    ((xiZeroWeight_summable hlog).mul_left (x ^ 2))

theorem integratedZeroTerm_norm_sum_le {x : ℝ} (hx : 0 < x) (hlog : 3100 ≤ Real.log x) :
    (∑' p, ‖integratedZeroTerm x p‖) ≤ (3 / 10000000) * x ^ 2 := by
  have h := (integratedZeroTerm_summable hx hlog).norm.tsum_le_tsum
    (integratedZeroTerm_norm_le hx) ((xiZeroWeight_summable hlog).mul_left (x ^ 2))
  rw [tsum_mul_left] at h
  have hsum := mul_le_mul_of_nonneg_left (xiZeroWeight_sum_le hlog) (sq_nonneg x)
  nlinarith only [h, hsum]

theorem integratedZeroSum_norm_le {x : ℝ} (hx : 0 < x) (hlog : 3100 ≤ Real.log x) :
    ‖∑' p, integratedZeroTerm x p‖ ≤ (3 / 10000000) * x ^ 2 :=
  (norm_tsum_le_tsum_norm (integratedZeroTerm_summable hx hlog).norm).trans
    (integratedZeroTerm_norm_sum_le hx hlog)

theorem integratedZeroSum_source_norm_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    ‖∑' p, integratedZeroTerm (N : ℝ) p‖ ≤ (3 / 10000000) * (N : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < N := (Real.exp_pos 3100).trans_le hN
  have hlog : 3100 ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hpos).2 hN
  exact integratedZeroSum_norm_le hpos hlog

theorem integratedZeroSum_difference_le {x : ℝ} (hx : 0 < x) (hlog : 3100 ≤ Real.log x) :
    ‖(∑' p, integratedZeroTerm (x + x / 1000) p) - ∑' p, integratedZeroTerm x p‖ ≤
      (6006003 / 10000000000000 : ℝ) * x ^ 2 := by
  have hy : 0 < x + x / 1000 := by positivity
  have hlogy : 3100 ≤ Real.log (x + x / 1000) :=
    hlog.trans (Real.log_le_log hx (by linarith))
  have h := (norm_sub_le (∑' p, integratedZeroTerm (x + x / 1000) p)
    (∑' p, integratedZeroTerm x p)).trans
    (add_le_add (integratedZeroSum_norm_le hy hlogy) (integratedZeroSum_norm_le hx hlog))
  nlinarith only [h]

theorem integrated_zero_desmoothing_budget {x : ℝ} (hx : 0 < x) :
    (x / 1000) / 2 +
      ((6006003 / 10000000000000 : ℝ) * x ^ 2) / (x / 1000) ≤ (12 / 10000) * x := by
  field_simp
  nlinarith

end LiuWang.Proof.ChebyshevBound.HighHeight
