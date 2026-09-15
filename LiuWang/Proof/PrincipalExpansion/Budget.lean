import LiuWang.Proof.PrincipalExpansion.Kernel

/-! # 实际误差斜率的 Abel 母式与强主字符实例 -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.NonprincipalExpansion

namespace LiuWang.Proof.PrincipalExpansion

def abelError (N : ℕ) (eta D : ℝ) : ℝ :=
  D * ((N : ℝ) + sourceWindowLower N) +
    Real.pi * |eta| * D * ((N : ℝ) ^ 2 - sourceWindowLower N ^ 2) + sourceL N

def errorFunction (c : ℝ) (N : ℕ) (eta : ℝ) : ℝ :=
  abelError N eta (c / sourceT N * sourceL N ^ 2)

theorem principal_error_of_slope {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (T eta D : ℝ)
    (hpsi : ∀ t ∈ Set.Icc (sourceWindowLower N) (N : ℝ),
      ‖ExplicitPerron.psi (1 : Character q) t - (t : ℂ) +
        PrincipalPsi.highZeroSum q t T‖ ≤ D * t) :
    ‖CharacterExpansion.twistedS N eta (1 : Character q) - J N eta + zeroSum q N T eta‖ ≤
      abelError N eta D := by
  rw [principal_error_identity (nat_pos_of_exp_le hN)]
  exact (norm_add_le _ _).trans (add_le_add (norm_abelTransform_le N eta _ hpsi)
    (norm_lowerTerm_le_log hN (1 : Character q) eta))

theorem principal_error_function {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖CharacterExpansion.twistedS N eta (1 : Character q) - J N eta +
      zeroSum q N (sourceT N) eta‖ ≤ errorFunction 0.962398 N eta := by
  apply principal_error_of_slope hN
  intro t ht
  convert PrincipalPsi.Quantitative.principal_psi_formula_recovered hN hq ht.1 ht.2 using 1
  ring

theorem modulus_one_error_function {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (eta : ℝ) :
    ‖CharacterExpansion.twistedS N eta (1 : Character 1) - J N eta +
      zeroSum 1 N (sourceT N) eta‖ ≤ errorFunction 0.962397 N eta := by
  apply principal_error_of_slope hN
  intro t ht
  convert PrincipalPsi.Quantitative.modulus_one_psi_formula_recovered hN ht.1 ht.2 using 1
  ring

theorem errorFunction_nonneg {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (eta : ℝ) : 0 ≤ errorFunction c N eta := by
  have hT := sourceT_pos hN
  have hL := sourceL_pos hN
  have ha := lower_nonneg N
  have hb := lower_le N
  have hquad : 0 ≤ (N : ℝ)^2 - sourceWindowLower N^2 := by nlinarith
  unfold errorFunction abelError
  positivity

theorem errorFunction_le_decimal {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (eta : ℝ) :
    errorFunction c N eta ≤
      (1.001 * c + 0.000001 + 3.1416 * c * (N : ℝ) * |eta|) *
        (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT := sourceT_pos hN
  have hquad : 0 ≤ (N : ℝ)^2 - sourceWindowLower N^2 := by
    have := lower_nonneg N
    have := lower_le N
    nlinarith
  have hpi :
      Real.pi * |eta| * (c / sourceT N * sourceL N ^ 2) *
          ((N : ℝ)^2 - sourceWindowLower N^2) ≤
        3.1416 * |eta| * (c / sourceT N * sourceL N ^ 2) * (N : ℝ)^2 := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right Real.pi_lt_d4.le (abs_nonneg eta))
        (by positivity)) hquad).trans
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)
  calc
    _ ≤ (c / sourceT N * sourceL N^2) * ((N : ℝ) + sourceWindowLower N) +
        3.1416 * |eta| * (c / sourceT N * sourceL N^2) * (N : ℝ)^2 +
        0.000001 * (N : ℝ) / sourceT N * sourceL N^2 :=
      add_le_add (add_le_add le_rfl hpi) (lowerTerm_cost_source_le hN)
    _ = _ := by unfold sourceWindowLower; ring

theorem principal_error_decimal {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N) (eta : ℝ) :
    ‖CharacterExpansion.twistedS N eta (1 : Character q) - J N eta +
      zeroSum q N (sourceT N) eta‖ ≤
      (0.963362 + 3.02347 * (N : ℝ) * |eta|) * (N : ℝ) / sourceT N * sourceL N^2 := by
  apply ((principal_error_function hN hq eta).trans
    (errorFunction_le_decimal (by norm_num) hN eta)).trans
  have hT := sourceT_pos hN
  have hscale : 0 ≤ (N : ℝ) / sourceT N * sourceL N^2 := by positivity
  have hc : 1.001 * (0.962398 : ℝ) + 0.000001 +
      3.1416 * 0.962398 * (N : ℝ) * |eta| ≤
        0.963362 + 3.02347 * (N : ℝ) * |eta| := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg eta)]
  simpa only [mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_right hc hscale

end LiuWang.Proof.PrincipalExpansion
