import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Difference

/-!
# 原 exp(3100) 阈值上的真实 psi ≤ 1.0012 x

采用 h=x/1000 的单侧去平滑。已付零点差分误差为
6006003*x²/10¹³，完整 Γ 修正差分范数至多 2*(2*x+h)。
原域蕴含 x≥10⁸，足以把全部误差纳入原 0.0012*x 预算。
-/

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

theorem exp_3100_ge_hundred_million : (100000000 : ℝ) ≤ Real.exp 3100 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3100) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem psi_le_sharp_real {x : ℝ} (hx : Real.exp 3100 ≤ x) :
    Chebyshev.psi x ≤ (1.0012 : ℝ) * x := by
  have hxlarge : (100000000 : ℝ) ≤ x := exp_3100_ge_hundred_million.trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlog : 3100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hh : 0 < x / 1000 := by positivity
  have hd := integratedPsi_difference_upper hx1 (y := x + x / 1000) (by linarith) hlog
  have hz := integratedZeroSum_difference_le hx0 hlog
  have hpaid : integratedPsi (x + x / 1000) - integratedPsi x ≤
      ((x + x / 1000) ^ 2 - x ^ 2) / 2 +
        (6006003 / 10000000000000 : ℝ) * x ^ 2 + 2 * (x + x / 1000 + x) := by
    linarith
  have hbudget : ((x + x / 1000) ^ 2 - x ^ 2) / 2 +
      (6006003 / 10000000000000 : ℝ) * x ^ 2 + 2 * (x + x / 1000 + x) ≤
        ((1.0012 : ℝ) * x) * (x / 1000) := by
    have hm := mul_nonneg (sub_nonneg.mpr hxlarge) hx0.le
    nlinarith
  exact (psi_le_integrated_difference hx0.le hh).trans
    ((div_le_iff₀ hh).2 (hpaid.trans hbudget))

theorem psi_le_sharp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    Chebyshev.psi (N : ℝ) ≤ (1.0012 : ℝ) * (N : ℝ) :=
  psi_le_sharp_real hN

theorem sum_mangoldt_Icc_le_sharp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n) ≤ (1.0012 : ℝ) * (N : ℝ) := by
  rw [sum_mangoldt_Icc_eq_psi]
  exact psi_le_sharp hN

theorem sum_mangoldt_Ioc_le_sharp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n) ≤ (1.0012 : ℝ) * (N : ℝ) := by
  simpa [Chebyshev.psi] using psi_le_sharp hN

theorem sum_mangoldt_sq_le_sharp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2) ≤
      (1.0012 : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have h := mul_le_mul_of_nonneg_left (psi_le_sharp hN) hlog
  exact (sum_mangoldt_sq_le_log_mul_psi N).trans (by nlinarith only [h])

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
