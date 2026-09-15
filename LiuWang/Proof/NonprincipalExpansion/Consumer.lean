import LiuWang.Proof.NonprincipalExpansion.Budget
import LiuWang.Proof.CharacterExpansion.Finite

/-!
# 全部非主字符的原闭窗振荡展开

实际消费已经验证的 `1.374172` psi 公式，不要求本原性。
本文件不包含主字符公式、完整 S 展开或 R12 的结论。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.FixedHeightZeroSum

namespace LiuWang.Proof.NonprincipalExpansion

theorem S_chi_eq_twistedS {q : ℕ} (N : ℕ) (chi : Character q) (η : ℝ) :
    S_chi N chi η = CharacterExpansion.twistedS N η chi := by
  simp only [S_chi, CharacterExpansion.twistedS, mul_comm η]

theorem nonprincipal_expansion_source_strong {N q : ℕ} [NeZero q]
    (chi : Character q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1) (η : ℝ) :
    ‖S_chi N chi η +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η‖ ≤
      (1.3756 + 4.3287 * (N : ℝ) * |η|) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hF : ∀ t ∈ Set.Icc (sourceWindowLower N) (N : ℝ),
      ‖ExplicitPerron.psi chi t + highZeroSum chi t (sourceT N)‖ ≤
        (1.374172 / sourceT N * sourceL N ^ 2) * t := by
    intro t ht
    convert NonprincipalPsi.psi_highZeroSum_source_le_strong
      chi hN hqUpper hchi ht.1 ht.2 using 1
    ring
  rw [expansion_error_identity (nat_pos_of_exp_le hN) hchi]
  exact ((norm_add_le _ _).trans (add_le_add
    (norm_abelTransform_le N η _ hF) (norm_lowerTerm_source_le hN chi η))).trans
      (source_abel_budget hN η)

theorem nonprincipal_expansion_source {N q : ℕ} [NeZero q]
    (chi : Character q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1) (η : ℝ) :
    ‖S_chi N chi η +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η‖ ≤
      (1.3818 + 4.3367 * (N : ℝ) * |η|) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  have hT0 := sourceT_pos hN
  have hs : 0 ≤ (N : ℝ) / sourceT N * sourceL N ^ 2 := by positivity
  have hc : 1.3756 + 4.3287 * (N : ℝ) * |η| ≤
      1.3818 + 4.3367 * (N : ℝ) * |η| := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (abs_nonneg η)]
  apply (nonprincipal_expansion_source_strong chi hN hqUpper hchi η).trans
  simpa only [mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_right hc hs

theorem nonprincipal_expansion {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 1 ≤ q)
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : Character q} (hchi : chi ≠ 1) (η : ℝ) :
    letI : NeZero q := ⟨by omega⟩
    ‖(∑ n ∈ windowFinset N,
        (ArithmeticFunction.vonMangoldt n : ℂ) * chi n * charReal (η * n)) +
      ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
        Jrho N (completedZeroValue p) η‖ ≤
      (1.3818 + 4.3367 * (N : ℝ) * |η|) * (N : ℝ) /
        (Real.log (N : ℝ)) ^ (15 : ℕ) * (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  let : NeZero q := ⟨by omega⟩
  exact nonprincipal_expansion_source chi hN hqUpper hchi η

theorem nonprincipal_twistedS_expansion {N q : ℕ} [NeZero q]
    (chi : Character q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1) (η : ℝ) :
    ‖CharacterExpansion.twistedS N η chi +
        ∑ p ∈ highZeroIndices chi (sourceT N), Jrho N (completedZeroValue p) η‖ ≤
      (1.3818 + 4.3367 * (N : ℝ) * |η|) * (N : ℝ) / sourceT N * sourceL N ^ 2 := by
  rw [← S_chi_eq_twistedS]
  exact nonprincipal_expansion_source chi hN hqUpper hchi η

end LiuWang.Proof.NonprincipalExpansion
