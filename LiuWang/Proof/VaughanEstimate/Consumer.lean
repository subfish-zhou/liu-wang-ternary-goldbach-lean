import LiuWang.Proof.VaughanEstimate.Main
import LiuWang.Proof.ParameterComparisons.FarArcScalar

/-! 真正取得远弧有理逼近，并将同一见证传给已闭合的 Vaughan 估计。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanEstimate

open Interfaces Parameters

/-- 原第四弧上的实际指数和界，不携带有理逼近或解析估计前提。 -/
theorem M4_norm_sourceS_le_margin {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ (0.294 : ℝ) * (N : ℝ) / sourceL N := by
  obtain ⟨q, a, θ, hqL, hqU, hi, hθ, heq, _⟩ :=
    ParameterComparisons.M4_exists_vaughan_approximation hN hα
  exact norm_sourceS_le_margin hN hqL.le hqU hi hθ heq

theorem M4_norm_sourceS_le_three_tenths {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ (0.3 : ℝ) * (N : ℝ) / sourceL N := by
  apply (M4_norm_sourceS_le_margin hN hα).trans
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  gcongr
  norm_num

/-- 展开真实闭窗口、Mangoldt权重和指数，不通过误差定义该有限和。 -/
theorem M4_closed_window_expSum_le {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * ((n : ℝ) * α) * Complex.I)‖ ≤
      (0.294 : ℝ) * (N : ℝ) / Real.log (N : ℝ) := by
  simpa only [S, Fourier.liuWangExpSum, Fourier.indexedExpSum,
    Fourier.liuWangSupport, AnalyticNumberTheory.LargeSieve.charReal,
    Int.cast_natCast, Complex.ofReal_mul, sourceL] using M4_norm_sourceS_le_margin hN hα

end LiuWang.Proof.VaughanEstimate
