import LiuWang.Proof.CompleteExpansion.Packet

/-! # 全 S 的实际 Gauss 质量与强误差母函数 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.PrincipalExpansion

namespace LiuWang.Proof.CompleteExpansion

def errorBound (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℝ :=
  principalMass q * errorFunction 0.962398 N eta +
    nonprincipalMass q a * PerronRecovery.oscillatoryError N eta +
      Real.log q * sourceL N / Real.log 2

theorem complete_error_function {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      zeroPacket q N a eta‖ ≤ errorBound q N a eta := by
  apply (complete_error_of_bounds N a eta _ _ hi.2.2
    (principal_error_function hN hq eta) (fun chi hc => ?_)).trans
  · exact add_le_add le_rfl
      (norm_nonCoprimeError_le_log (nat_pos_of_exp_le hN) (NeZero.pos q) _)
  · rw [← NonprincipalExpansion.S_chi_eq_twistedS]
    exact PerronRecovery.nonprincipal_oscillation_function chi hN hq hc eta

theorem errorBound_le_decimal {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (a : ℕ) (eta : ℝ) :
    errorBound q N a eta ≤
      (principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        nonprincipalMass q a * (0.96258 + 3.02102 * (N : ℝ) * |eta|)) *
          (N : ℝ) / sourceT N * sourceL N^2 +
        Real.log q * sourceL N / Real.log 2 := by
  have hT := sourceT_pos hN
  have hscale : 0 ≤ (N : ℝ) / sourceT N * sourceL N^2 := by positivity
  have hc : 1.001 * (0.962398 : ℝ) + 0.000001 +
      3.1416 * 0.962398 * (N : ℝ) * |eta| ≤
        0.963362 + 3.02347 * (N : ℝ) * |eta| := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg eta)]
  have hp : errorFunction 0.962398 N eta ≤
      (0.963362 + 3.02347 * (N : ℝ) * |eta|) *
        (N : ℝ) / sourceT N * sourceL N^2 := by
    apply (errorFunction_le_decimal (by norm_num) hN eta).trans
    simpa only [mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_right hc hscale
  calc
    _ ≤ principalMass q *
        ((0.963362 + 3.02347 * (N : ℝ) * |eta|) * (N : ℝ) / sourceT N * sourceL N^2) +
      nonprincipalMass q a *
        ((0.96258 + 3.02102 * (N : ℝ) * |eta|) * (N : ℝ) / sourceT N * sourceL N^2) +
      Real.log q * sourceL N / Real.log 2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp (principalMass_nonneg q))
        (mul_le_mul_of_nonneg_left (PerronRecovery.oscillatoryError_le hN eta)
          (nonprincipalMass_nonneg q a))) le_rfl
    _ = _ := by ring

theorem complete_error_decimal {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      zeroPacket q N a eta‖ ≤
      (principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        nonprincipalMass q a * (0.96258 + 3.02102 * (N : ℝ) * |eta|)) *
          (N : ℝ) / sourceT N * sourceL N^2 +
        Real.log q * sourceL N / Real.log 2 :=
  (complete_error_function hN hi hq eta).trans (errorBound_le_decimal hN a eta)

theorem complete_error_totient {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      zeroPacket q N a eta‖ ≤
      (principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        Real.sqrt (q.totient : ℝ) * (0.96258 + 3.02102 * (N : ℝ) * |eta|)) *
          (N : ℝ) / sourceT N * sourceL N^2 +
        Real.log q * sourceL N / Real.log 2 := by
  apply (complete_error_decimal hN hi hq eta).trans
  have hT := sourceT_pos hN
  gcongr
  exact nonprincipalMass_le_totient q a

theorem complete_error_modulus {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
      zeroPacket q N a eta‖ ≤
      (principalMass q * (0.963362 + 3.02347 * (N : ℝ) * |eta|) +
        Real.sqrt (q : ℝ) * (0.96258 + 3.02102 * (N : ℝ) * |eta|)) *
          (N : ℝ) / sourceT N * sourceL N^2 +
        Real.log q * sourceL N / Real.log 2 := by
  apply (complete_error_decimal hN hi hq eta).trans
  have hT := sourceT_pos hN
  gcongr
  exact nonprincipalMass_le_modulus q a

@[simp] theorem errorBound_one (N a : ℕ) (eta : ℝ) :
    errorBound 1 N a eta = errorFunction 0.962398 N eta := by
  simp [errorBound]

theorem complete_modulus_one_function {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (a : ℕ) (eta : ℝ) :
    ‖S N (rationalCenter a 1 + eta) - J N eta +
      PrincipalExpansion.zeroSum 1 N (sourceT N) eta‖ ≤ errorFunction 0.962397 N eta := by
  rw [NonprincipalPacket.S_modulus_one]
  exact modulus_one_error_function hN eta

end LiuWang.Proof.CompleteExpansion
