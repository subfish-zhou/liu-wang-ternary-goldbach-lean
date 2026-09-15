import LiuWang.Proof.NonprincipalPsi.InductionBudget
import LiuWang.Proof.NonprincipalPsi.ZeroTransport

/-!
# 全部非主字符的原 psi 闭高零点公式

实际 ambient chi 的 psi 与保重数零点和；不要求本原性，不暴露高度或运输前提。
保留接线所得 1.374172 强界，并给出原要求的 1.3804 消费者。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.FixedHeightZeroSum

namespace LiuWang.Proof.NonprincipalPsi

theorem psi_highZeroSum_source_le_strong {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi chi t + highZeroSum chi t (sourceT N)‖ ≤
      1.374172 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [highZeroSum_eq_primitive chi hchi]
  exact psi_primitive_highZeroSum_source_le chi hN hqUpper hchi htlo hthi

theorem psi_highZeroSum_source_le {N q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ sourceP1 N) (hchi : chi ≠ 1)
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi chi t + highZeroSum chi t (sourceT N)‖ ≤
      1.3804 * t / sourceT N * sourceL N ^ (2 : ℕ) := by
  have ht0 : 0 ≤ t := by
    linarith [(PerronBudget.source_cutoff_bounds hN htlo hthi).1]
  have hscale : 0 ≤ t / sourceT N * sourceL N ^ (2 : ℕ) := by
    have := (sourceT_pos hN).le
    positivity
  calc
    _ ≤ 1.374172 * t / sourceT N * sourceL N ^ (2 : ℕ) :=
      psi_highZeroSum_source_le_strong chi hN hqUpper hchi htlo hthi
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right
        (by norm_num : (1.374172 : ℝ) ≤ 1.3804) hscale
      simpa only [mul_assoc, mul_div_assoc] using hh

theorem nonprincipal_psi_sum_strong {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (t : ℂ) ^ completedZeroValue p / completedZeroValue p‖ ≤
      1.374172 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  simpa only [ExplicitPerron.psi_eq_sum, highZeroSum, sourceL, sourceT] using
    psi_highZeroSum_source_le_strong chi hN hqUpper hchi htlo hthi

theorem nonprincipal_psi_sum {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 1 ≤ q)
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    letI : NeZero q := ⟨by omega⟩
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ p ∈ highZeroIndices chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (t : ℂ) ^ completedZeroValue p / completedZeroValue p‖ ≤
      1.3804 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  let : NeZero q := ⟨by omega⟩
  simpa only [ExplicitPerron.psi_eq_sum, highZeroSum, sourceL, sourceT] using
    psi_highZeroSum_source_le chi hN hqUpper hchi htlo hthi

theorem nonprincipal_psi_sum_multiplicity_strong {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hqUpper : (q : ℝ) ≤ (Real.log (N : ℝ)) ^ (6 : ℕ))
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {t : ℝ} (htlo : (N : ℝ) / 1000 ≤ t) (hthi : t ≤ (N : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) +
        ∑ rho ∈ highZeroValues chi ((Real.log (N : ℝ)) ^ (15 : ℕ)),
          (analyticOrderNatAt chi.LFunction rho : ℂ) * ((t : ℂ) ^ rho / rho)‖ ≤
      1.374172 * t / (Real.log (N : ℝ)) ^ (15 : ℕ) *
        (Real.log (N : ℝ)) ^ (2 : ℕ) := by
  rw [sum_highZeroValues_multiplicity hchi]
  exact nonprincipal_psi_sum_strong hN hqUpper hchi htlo hthi

end LiuWang.Proof.NonprincipalPsi
