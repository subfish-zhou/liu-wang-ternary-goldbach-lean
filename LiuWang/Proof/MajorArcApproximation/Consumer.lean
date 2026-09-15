import LiuWang.Proof.MajorArcApproximation.Interaction

/-! # 实际 M1 三次近似、普通 L 闭窗与有号相互作用消费者 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.MajorArcApproximation

theorem packet_eq_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    packet N a q eta = (q.totient : ℂ)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q, CharacterExpansion.G a chi *
        ∑ rho ∈ zeroValues chi (sourceT N),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  rw [packet_eq, zeroPacket_eq_all_values N a eta haq]
  rfl

theorem packet_closed_window {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (N : ℕ) (rho : ℂ) :
    rho ∈ zeroValues chi (sourceT N) ↔
      chi.LFunction rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧
        |rho.im| ≤ sourceT N ∧ 1/2 ≤ rho.re :=
  mem_zeroValues

theorem model_eq_values {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ)
    (haq : Nat.Coprime a q) :
    model N a q eta =
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * J N eta -
        (q.totient : ℂ)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q, CharacterExpansion.G a chi *
            ∑ rho ∈ zeroValues chi (sourceT N),
              (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  rw [model_eq_main_sub_packet, packet_eq_values N a eta haq]
  rfl

theorem model_one (N a : ℕ) (eta : ℝ) :
    model N a 1 eta = J N eta -
      PrincipalExpansion.zeroSum 1 N (sourceT N) eta := by
  rw [model_eq]
  simp

theorem core_strong_error {N a q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ}
    (heta : |eta| ≤ deltaRadius N q) :
    ‖S N (rationalCenter a q + eta) - model N a q eta‖ ≤
      20 * (N : ℝ) / sourceL N^10 := by
  let : NeZero q := ⟨Nat.ne_of_gt (ArcGeometry.sourceIndex_den_pos hi)⟩
  apply (norm_S_sub_model hN hi (hq.trans (sourceP_le_sourceP1 hN)) eta).trans
  simpa only [epsilon_eq] using epsilon_le_core hN hi hq heta

theorem major_arc_approximation {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖(∫ alpha in M1 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)) -
      ∑ q ∈ denominators (sourceP N), ∑ a ∈ numerators q,
        ∫ eta in -deltaRadius N q..deltaRadius N q,
          (principalCoefficient q * J N eta - packet N a q eta)^3 *
            charReal (-(N : ℝ)*(rationalCenter a q + eta))‖ ≤
      6760 * (N : ℝ)^2 / sourceL N^4 := by
  simpa only [majorIntegral, modelIntegral, coreIndices, Finset.sum_sigma,
    model_eq_main_sub_packet, arcPhase] using norm_major_sub_model_le_log_power hN

theorem major_arc_with_signed_zeros {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖(∫ alpha in M1 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)) -
      (I11 N +
        ∑ q ∈ denominators (sourceP N), ∑ a ∈ numerators q,
          ∫ eta in -deltaRadius N q..deltaRadius N q,
            (-3 * (principalCoefficient q * J N eta)^2 * packet N a q eta +
              3 * (principalCoefficient q * J N eta) * packet N a q eta^2 -
                packet N a q eta^3) *
              charReal (-(N : ℝ)*(rationalCenter a q + eta)))‖ ≤
      6760 * (N : ℝ)^2 / sourceL N^4 := by
  have hh := (norm_major_sub_I11_interaction hN).trans (errorIntegral_le_log_power hN)
  simpa only [majorIntegral, interactionIntegral, interactionKernel, coreIndices,
    Finset.sum_sigma, arcPhase] using hh

theorem major_arc_with_signed_zeros_decimal {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    ‖majorIntegral N - (I11 N + interactionIntegral N)‖ ≤ 0.000000001 * (N : ℝ)^2 :=
  ((norm_major_sub_I11_interaction hN).trans (errorIntegral_le_log_power hN)).trans
    (log_power_le_decimal hN)

theorem major_arc_re_strong {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (hodd : Odd N) :
    0.65617 * (N : ℝ)^2 + (interactionIntegral N).re -
      6760 * (N : ℝ)^2 / sourceL N^4 ≤
        (∫ alpha in M1 N, S N alpha^3 * charReal (-(N : ℝ)*alpha)).re :=
  re_major_lower_strong hN hodd

end LiuWang.Proof.MajorArcApproximation
