import LiuWang.Proof.NonprincipalExpansion.Consumer

/-!
# 非约化项的一次付款

直接复用已验的百万倍高度平方余量，不重做 N 与对数幂的增长链。
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.NonprincipalPacket

theorem nonCoprime_cost_source_le {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sourceL N ^ 2 / Real.log 2 ≤
      0.0001 * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT0 := sourceT_pos hN
  have hT1 : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hinv : (1 : ℝ) / Real.log 2 ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    linarith
  have hpay : 2 ≤ 0.0001 * (N : ℝ) / sourceT N := by
    apply (le_div_iff₀ hT0).mpr
    have hh := PerronBudget.million_sourceT_sq_le_endpoint hN
      (NonprincipalExpansion.lower_le N)
    nlinarith [mul_nonneg (sub_nonneg.mpr hT1) hT0.le]
  calc
    _ = (1 / Real.log 2) * sourceL N ^ 2 := by ring
    _ ≤ 2 * sourceL N ^ 2 :=
      mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hpay (sq_nonneg _)

theorem one_le_sqrt_modulus {q : ℕ} (hq : 1 ≤ q) :
    1 ≤ Real.sqrt (q : ℝ) := by
  simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ q by exact_mod_cast hq)

theorem norm_nonCoprimeError_packet_le {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 1 ≤ q)
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (α : ℝ) :
    ‖CharacterExpansion.nonCoprimeError N q α‖ ≤
      0.0001 * Real.sqrt (q : ℝ) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT0 := sourceT_pos hN
  calc
    _ ≤ sourceL N ^ 2 / Real.log 2 :=
      CharacterExpansion.norm_nonCoprimeError_le_source hN hq hqUpper α
    _ ≤ 0.0001 * (N : ℝ) / sourceT N * sourceL N ^ 2 :=
      nonCoprime_cost_source_le hN
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (one_le_sqrt_modulus hq)
        (show 0 ≤ 0.0001 * (N : ℝ) / sourceT N * sourceL N ^ 2 by positivity)
      calc
        _ ≤ Real.sqrt (q : ℝ) *
            (0.0001 * (N : ℝ) / sourceT N * sourceL N ^ 2) := by
          simpa only [one_mul] using h
        _ = _ := by ring

end LiuWang.Proof.NonprincipalPacket
