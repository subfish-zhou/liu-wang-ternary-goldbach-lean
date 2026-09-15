import LiuWang.Proof.PrincipalExpansion.Budget

/-! # 普通 L 真实重数与原字面闭窗的强主字符振荡消费者 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.PrincipalExpansion

theorem principal_twisted_values {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖CharacterExpansion.twistedS N eta (1 : Character q) - J N eta +
      ∑ rho ∈ PrincipalPsi.highZeroValues q (sourceT N),
        (analyticOrderNatAt (1 : Character q).LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      errorFunction 0.962398 N eta := by
  rw [← zeroSum_eq_values]
  exact principal_error_function hN hq eta

theorem principal_closed_window {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^6)
    (eta : ℝ) :
    ‖(∑ n ∈ windowFinset N,
        (ArithmeticFunction.vonMangoldt n : ℂ) * (1 : Character q) n * charReal (eta * n)) -
      J N eta +
      ∑ rho ∈ PrincipalPsi.highZeroValues q ((Real.log (N : ℝ))^15),
        (analyticOrderNatAt (1 : Character q).LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (0.963362 + 3.02347 * (N : ℝ) * |eta|) * (N : ℝ) /
        (Real.log (N : ℝ))^15 * (Real.log (N : ℝ))^2 := by
  have h := principal_error_decimal hN hq eta
  rw [zeroSum_eq_values, ← NonprincipalExpansion.S_chi_eq_twistedS] at h
  exact h

theorem principal_zero_window {q : ℕ} [NeZero q] {T : ℝ} {rho : ℂ} :
    rho ∈ PrincipalPsi.highZeroValues q T ↔
      (1 : Character q).LFunction rho = 0 ∧
        0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ T ∧ 1 / 2 ≤ rho.re :=
  PrincipalPsi.mem_highZeroValues

end LiuWang.Proof.PrincipalExpansion
