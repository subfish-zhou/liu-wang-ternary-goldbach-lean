import LiuWang.Proof.VaughanRecovery.Main

/-! 真实闭窗口与原 Mangoldt 权重的强消费者，旧常数仅作兼容推论。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters

theorem M4_closed_window_mother {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * ((n : ℝ) * α) * Complex.I)‖ ≤
      mother N 0.1939 3.318 0.0883 := by
  simpa only [S, Fourier.liuWangExpSum, Fourier.indexedExpSum,
    Fourier.liuWangSupport, AnalyticNumberTheory.LargeSieve.charReal,
    Int.cast_natCast, Complex.ofReal_mul] using M4_le_mother hN hα

theorem M4_closed_window_194 {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * ((n : ℝ) * α) * Complex.I)‖ ≤
      0.194 * (N : ℝ) / Real.log (N : ℝ) := by
  simpa only [S, Fourier.liuWangExpSum, Fourier.indexedExpSum,
    Fourier.liuWangSupport, AnalyticNumberTheory.LargeSieve.charReal,
    Int.cast_natCast, Complex.ofReal_mul, sourceL] using M4_le_194 hN hα

theorem M4_le_294 {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ 0.294 * (N : ℝ) / sourceL N := by
  apply (M4_le_1743 hN hα).trans
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  gcongr
  norm_num

theorem M4_le_300 {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖S N α‖ ≤ 0.3 * (N : ℝ) / sourceL N := by
  apply (M4_le_294 hN hα).trans
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  gcongr
  norm_num

theorem M4_closed_window_repaid_mother {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * ((n : ℝ) * α) * Complex.I)‖ ≤
      mother N 0.1741355 3.2354175 0.077006 := by
  simpa only [S, Fourier.liuWangExpSum, Fourier.indexedExpSum,
    Fourier.liuWangSupport, AnalyticNumberTheory.LargeSieve.charReal,
    Int.cast_natCast, Complex.ofReal_mul] using M4_le_repaid_mother hN hα

theorem M4_closed_window_1743 {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * ((n : ℝ) * α) * Complex.I)‖ ≤
      0.1743 * (N : ℝ) / Real.log (N : ℝ) := by
  simpa only [S, Fourier.liuWangExpSum, Fourier.indexedExpSum,
    Fourier.liuWangSupport, AnalyticNumberTheory.LargeSieve.charReal,
    Int.cast_natCast, Complex.ofReal_mul, sourceL] using M4_le_1743 hN hα

theorem M4_closed_window_repaid_explicit {N : ℕ} {α : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hα : α ∈ M4 N) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n => N ≤ 1000 * n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * ((n : ℝ) * α) * Complex.I)‖ ≤
      0.1741355 * (N : ℝ) / sourceL N +
        3.2354175 * (N : ℝ) ^ ((4 : ℝ) / 5) * sourceL N ^ ((7 : ℝ) / 5) +
        0.077006 * (N : ℝ) ^ ((1 : ℝ) / 2) * sourceL N ^ ((11 : ℝ) / 2) := by
  have hs := M4_closed_window_repaid_mother hN hα
  rw [mother_eq (exp_2000_le_of_exp_3100_le hN)] at hs
  simpa only [VaughanTypeIIBudget.termB, mul_assoc] using hs

end LiuWang.Proof.VaughanRecovery
