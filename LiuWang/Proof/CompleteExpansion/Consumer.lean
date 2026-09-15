import LiuWang.Proof.CompleteExpansion.Values
import LiuWang.Proof.CharacterExpansion.Main

/-! # 实际全 S：字面闭窗、全部普通 L 重数与更强母函数 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.CompleteExpansion

theorem complete_values_function {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * J N eta +
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
        ∑ rho ∈ zeroValues chi (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      errorBound q N a eta := by
  have h := complete_error_function hN hi hq eta
  rw [zeroPacket_eq_all_values N a eta hi.2.2] at h
  exact h

theorem S_eq_closed_sum (N : ℕ) (alpha : ℝ) :
    S N alpha = ∑ n ∈ windowFinset N,
      (ArithmeticFunction.vonMangoldt n : ℂ) * charReal ((n : ℝ) * alpha) := by
  rw [← twistedS_one N alpha (1 : Character 1)]
  simp only [twistedS, character_level_one_apply, mul_one]

theorem window_eq_literal (N : ℕ) :
    (windowFinset N : Set ℕ) = {n : ℕ | (N : ℝ) / 1000 ≤ (n : ℝ) ∧ n ≤ N} := by
  ext n
  exact NonprincipalExpansion.mem_window_real N n

theorem complete_closed_window {N a q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ (Real.log (N : ℝ))^6) (eta : ℝ) :
    let : NeZero q := ⟨by have := hi.1.trans hi.2.1; omega⟩
    ‖(∑ n ∈ windowFinset N, (ArithmeticFunction.vonMangoldt n : ℂ) *
        charReal ((n : ℝ) * ((a : ℝ) / (q : ℝ) + eta))) -
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
        (∫ t in (N : ℝ)/1000..(N : ℝ), charReal (eta * t)) +
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
        ∑ rho ∈ zeroValues chi ((Real.log (N : ℝ))^15),
          (analyticOrderNatAt chi.LFunction rho : ℂ) *
            (∫ t in (N : ℝ)/1000..(N : ℝ), (t : ℂ)^(rho - 1) * charReal (eta * t))‖ ≤
      (|(ArithmeticFunction.moebius q : ℝ)| / (q.totient : ℝ) *
          (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        ((q.totient : ℝ)⁻¹ *
          ∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1, ‖G a chi‖) *
          (0.96258 + 3.02102 * (N : ℝ) * |eta|)) *
            (N : ℝ) / (Real.log (N : ℝ))^15 * (Real.log (N : ℝ))^2 +
        Real.log q * Real.log N / Real.log 2 := by
  let : NeZero q := ⟨by have := hi.1.trans hi.2.1; omega⟩
  have h := complete_error_decimal hN hi hq eta
  rw [S_eq_closed_sum, zeroPacket_eq_all_values N a eta hi.2.2] at h
  exact h

theorem complete_values_totient {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
        ∑ rho ∈ zeroValues chi (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        Real.sqrt (q.totient : ℝ) * (0.96258 + 3.02102 * (N : ℝ) * |eta|)) *
          (N : ℝ) / sourceT N * sourceL N^2 + Real.log q * sourceL N / Real.log 2 := by
  have h := complete_error_totient hN hi hq eta
  rw [zeroPacket_eq_all_values N a eta hi.2.2] at h
  exact h

theorem complete_modulus_one_values {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (a : ℕ) (eta : ℝ) :
    ‖S N (rationalCenter a 1 + eta) - J N eta +
      ∑ rho ∈ zeroValues (1 : Character 1) (sourceT N),
        (analyticOrderNatAt (1 : Character 1).LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      PrincipalExpansion.errorFunction 0.962397 N eta := by
  change ‖_ - _ + zeroValueSum (1 : Character 1) N (sourceT N) eta‖ ≤ _
  rw [zeroValueSum_principal]
  exact complete_modulus_one_function hN a eta

theorem modulus_one_corrections (N a : ℕ) (eta : ℝ) :
    NonprincipalPacket.Znp (q := 1) N a eta = 0 ∧
      nonprincipalMass 1 a = 0 ∧
      nonCoprimeError N 1 (rationalCenter a 1 + eta) = 0 ∧
      Real.log (1 : ℝ) * sourceL N / Real.log 2 = 0 := by
  simp

end LiuWang.Proof.CompleteExpansion
