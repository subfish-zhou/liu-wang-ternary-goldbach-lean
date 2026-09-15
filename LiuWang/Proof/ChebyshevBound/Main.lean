import LiuWang.Proof.ChebyshevBound.ZetaLocal
import LiuWang.Proof.Parameters.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries

/-!
# 已付解析前缀：原域右垂直线上的实际 Λ 级数

证明全素数幂 Dirichlet 级数在 b = 1 + 1/log N 处不超过 log N + 8。
这是带 n^(-b) 权重的无穷和，不是 ψ(N) ≤ 1.0012 N。
高于低高度矩形的显式 ζ 零区、相应零点总量与去平滑仍未支付。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ChebyshevBound

open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

theorem summable_mangoldt_dirichlet {b : ℝ} (hb : 1 < b) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ b) := by
  simpa only [norm_LSeriesTerm_vonMangoldt_eq] using
    (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (b : ℂ)) (by simpa using hb)).norm

theorem mangoldt_dirichlet_le_inv_add_eight {b : ℝ} (hb : 1 < b) (hb' : b ≤ 5 / 4) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ b) ≤
      1 / (b - 1) + 8 := by
  have heq : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ b) =
      vonMangoldtLSeriesNormSum b := by
    simp only [vonMangoldtLSeriesNormSum, norm_LSeriesTerm_vonMangoldt_eq]
  rw [heq, vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re hb]
  calc
    _ ≤ ‖-deriv riemannZeta (b : ℂ) / riemannZeta (b : ℂ)‖ := Complex.re_le_norm _
    _ = ‖logDeriv riemannZeta (b : ℂ)‖ := by
      rw [neg_div, norm_neg, logDeriv_apply]
    _ ≤ _ := norm_logDeriv_riemannZeta_real_le hb hb'

theorem source_abscissa_mem {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 < 1 + 1 / sourceL N ∧ 1 + 1 / sourceL N ≤ 5 / 4 := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  constructor
  · linarith [one_div_pos.mpr hL0]
  · have hsmall : 1 / sourceL N ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith

theorem mangoldt_dirichlet_source_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
      (n : ℝ) ^ (1 + 1 / sourceL N)) ≤ sourceL N + 8 := by
  have hb := source_abscissa_mem hN
  simpa only [add_sub_cancel_left, one_div, inv_inv] using
    mangoldt_dirichlet_le_inv_add_eight hb.1 hb.2

end LiuWang.Proof.ChebyshevBound
