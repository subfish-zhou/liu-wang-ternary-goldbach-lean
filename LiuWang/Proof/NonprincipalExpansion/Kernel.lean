import LiuWang.Proof.NonprincipalExpansion.Abel

/-!
# 固定有限零点和的精确振荡核运输

每项在正实区间连续可积；先固定保重数索引，再交换有限和与积分。
这里没有对逐个零点使用三角不等式。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Interval
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.OscillatoryBounds LiuWang.Proof.FixedHeightZeroSum

namespace LiuWang.Proof.NonprincipalExpansion

theorem cpow_div_hasDerivAt {rho : ℂ} (hrho : rho ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ rho / rho) ((t : ℂ) ^ (rho - 1)) t := by
  simpa only [mul_div_cancel_left₀ _ hrho] using
    (hasDerivAt_ofReal_cpow_const ht.ne' hrho).div_const rho

theorem cpow_continuousOn {a b : ℝ} (ha : 0 < a) (rho : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ rho) (Set.Icc a b) := by
  intro t ht
  exact (Complex.continuousAt_ofReal_cpow_const t rho
    (Or.inr (ne_of_gt (ha.trans_le ht.1)))).continuousWithinAt

theorem cpow_phase_integrable {N : ℕ} (hN : 0 < N) (rho : ℂ) (η : ℝ) :
    IntervalIntegrable (fun t => phaseDerivative η t * ((t : ℂ) ^ rho / rho))
      volume (sourceWindowLower N) N := by
  have ha : 0 < sourceWindowLower N := by unfold sourceWindowLower; positivity
  exact ((phaseDerivative_continuous η).continuousOn.mul
    ((cpow_continuousOn ha rho).div_const rho)).intervalIntegrable_of_Icc (lower_le N)

theorem Jrho_eq_abelTransform {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hrho : rho ≠ 0) (η : ℝ) :
    Jrho N rho η = abelTransform N η (fun t => (t : ℂ) ^ rho / rho) := by
  have ha : 0 < sourceWindowLower N := by unfold sourceWindowLower; positivity
  have hp : ∀ t ∈ Set.uIcc (sourceWindowLower N) (N : ℝ),
      HasDerivAt (fun x : ℝ => (x : ℂ) ^ rho / rho) ((t : ℂ) ^ (rho - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le (lower_le N)] at ht
    exact cpow_div_hasDerivAt hrho (ha.trans_le ht.1)
  have hi : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (rho - 1))
      volume (sourceWindowLower N) N :=
    (cpow_continuousOn ha (rho - 1)).intervalIntegrable_of_Icc (lower_le N)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hasDerivAt_charReal_mul η t) hp
    ((phaseDerivative_continuous η).intervalIntegrable _ _) hi
  simpa only [Jrho, abelTransform, phaseDerivative, mul_comm,
    Complex.ofReal_natCast] using h

theorem abelTransform_sum {ι : Type*} (s : Finset ι) (N : ℕ) (η : ℝ)
    (F : ι → ℝ → ℂ)
    (hi : ∀ p ∈ s, IntervalIntegrable (fun t => phaseDerivative η t * F p t)
      volume (sourceWindowLower N) N) :
    abelTransform N η (fun t => ∑ p ∈ s, F p t) =
      ∑ p ∈ s, abelTransform N η (F p) := by
  simp only [abelTransform, Finset.mul_sum, Finset.sum_sub_distrib,
    intervalIntegral.integral_finsetSum hi]

theorem high_zero_ne_zero {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (T : ℝ) (p : CompletedZeroIndex chi)
    (hp : p ∈ highZeroIndices chi T) : completedZeroValue p ≠ 0 := by
  have hre := ((NonprincipalPsi.mem_highZeroIndices_nonprincipal hchi T p).mp hp).2
  intro h
  rw [h, Complex.zero_re] at hre
  norm_num at hre

theorem highZeroSum_phase_integrable {N q : ℕ} [NeZero q]
    (hN : 0 < N) (chi : Character q) (T η : ℝ) :
    IntervalIntegrable (fun t => phaseDerivative η t * highZeroSum chi t T)
      volume (sourceWindowLower N) N := by
  simp only [highZeroSum, Finset.mul_sum]
  convert! IntervalIntegrable.sum (highZeroIndices chi T)
    (fun (p : CompletedZeroIndex chi) _ => cpow_phase_integrable hN (completedZeroValue p) η)
    using 1
  ext t
  simp only [Finset.sum_apply]

theorem sum_Jrho_eq_abelTransform {N q : ℕ} [NeZero q]
    (hN : 0 < N) {chi : Character q} (hchi : chi ≠ 1) (T η : ℝ) :
    (∑ p ∈ highZeroIndices chi T, Jrho N (completedZeroValue p) η) =
      abelTransform N η (fun t => highZeroSum chi t T) := by
  unfold highZeroSum
  rw [abelTransform_sum _ N η _
    (fun p _ => cpow_phase_integrable hN (completedZeroValue p) η)]
  apply Finset.sum_congr rfl
  intro p hp
  exact Jrho_eq_abelTransform hN (high_zero_ne_zero hchi T p hp) η

theorem expansion_error_identity {N q : ℕ} [NeZero q]
    (hN : 0 < N) {chi : Character q} (hchi : chi ≠ 1) (T η : ℝ) :
    S_chi N chi η + ∑ p ∈ highZeroIndices chi T, Jrho N (completedZeroValue p) η =
      abelTransform N η (fun t => ExplicitPerron.psi chi t + highZeroSum chi t T) +
        lowerTerm N (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * chi n) η := by
  rw [S_chi_abel, sum_Jrho_eq_abelTransform hN hchi,
    abelTransform_add _ _ _ _ (psi_phase_integrable N chi η)
      (highZeroSum_phase_integrable hN chi T η)]
  ring

end LiuWang.Proof.NonprincipalExpansion
