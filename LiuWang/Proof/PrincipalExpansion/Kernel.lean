import LiuWang.Proof.PrincipalPsi.Quantitative.Strong
import LiuWang.Proof.NonprincipalExpansion.Kernel

/-! # 主字符原闭窗的精确 Abel 恒等式与主项消去 -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.NonprincipalExpansion
open LiuWang.Proof.PrincipalPsi

namespace LiuWang.Proof.PrincipalExpansion

def zeroSum (q : ℕ) [NeZero q] (N : ℕ) (T eta : ℝ) : ℂ :=
  ∑ p ∈ PrincipalPsi.highZeroIndices q T, Jrho N (principalZeroValue p) eta

theorem zeroSum_eq_values (q : ℕ) [NeZero q] (N : ℕ) (T eta : ℝ) :
    zeroSum q N T eta =
      ∑ rho ∈ PrincipalPsi.highZeroValues q T,
        (analyticOrderNatAt (1 : Character q).LFunction rho : ℂ) * Jrho N rho eta :=
  (sum_highZeroValues_multiplicity q T (fun rho => Jrho N rho eta)).symm

theorem J_eq_abelTransform {N : ℕ} (hN : 0 < N) (eta : ℝ) :
    J N eta = abelTransform N eta (fun t => (t : ℂ)) := by
  simpa only [Jrho, J, sub_self, Complex.cpow_zero, one_mul, Complex.cpow_one, div_one] using
    Jrho_eq_abelTransform hN (show (1 : ℂ) ≠ 0 by norm_num) eta

theorem identity_phase_integrable (N : ℕ) (eta : ℝ) :
    IntervalIntegrable (fun t : ℝ => phaseDerivative eta t * (t : ℂ))
      volume (sourceWindowLower N) N :=
  ((phaseDerivative_continuous eta).mul Complex.continuous_ofReal).intervalIntegrable _ _

theorem abelTransform_sub (N : ℕ) (eta : ℝ) (F G : ℝ → ℂ)
    (hF : IntervalIntegrable (fun t => phaseDerivative eta t * F t)
      volume (sourceWindowLower N) N)
    (hG : IntervalIntegrable (fun t => phaseDerivative eta t * G t)
      volume (sourceWindowLower N) N) :
    abelTransform N eta (fun t => F t - G t) =
      abelTransform N eta F - abelTransform N eta G := by
  simp only [abelTransform, mul_sub, intervalIntegral.integral_sub hF hG]
  ring

theorem principal_highZeroSum_phase_integrable {N : ℕ} (hN : 0 < N)
    (q : ℕ) [NeZero q] (T eta : ℝ) :
    IntervalIntegrable (fun t => phaseDerivative eta t * PrincipalPsi.highZeroSum q t T)
      volume (sourceWindowLower N) N := by
  simp only [PrincipalPsi.highZeroSum, Finset.mul_sum]
  convert! IntervalIntegrable.sum (PrincipalPsi.highZeroIndices q T)
    (fun (p : PrincipalZeroIndex q) _ => cpow_phase_integrable hN (principalZeroValue p) eta)
    using 1
  ext t
  simp only [Finset.sum_apply]

theorem zeroSum_eq_abelTransform {N : ℕ} (hN : 0 < N)
    (q : ℕ) [NeZero q] (T eta : ℝ) :
    zeroSum q N T eta = abelTransform N eta (fun t => PrincipalPsi.highZeroSum q t T) := by
  unfold zeroSum PrincipalPsi.highZeroSum
  rw [abelTransform_sum _ N eta _
    (fun p _ => cpow_phase_integrable hN (principalZeroValue p) eta)]
  apply Finset.sum_congr rfl
  intro p hp
  have hre := (PrincipalPsi.mem_highZeroIndices.mp hp).1.1
  have hn : principalZeroValue p ≠ 0 := by intro h; simp [h] at hre
  exact Jrho_eq_abelTransform hN hn eta

theorem principal_error_identity {N : ℕ} (hN : 0 < N)
    (q : ℕ) [NeZero q] (T eta : ℝ) :
    CharacterExpansion.twistedS N eta (1 : Character q) - J N eta + zeroSum q N T eta =
      abelTransform N eta
        (fun t => ExplicitPerron.psi (1 : Character q) t - (t : ℂ) +
          PrincipalPsi.highZeroSum q t T) +
        lowerTerm N (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (1 : Character q) n) eta := by
  rw [← S_chi_eq_twistedS, S_chi_abel, J_eq_abelTransform hN,
    zeroSum_eq_abelTransform hN]
  rw [abelTransform_add _ _ _ _
    (by simpa only [mul_sub] using
      (psi_phase_integrable N (1 : Character q) eta).sub (identity_phase_integrable N eta))
    (principal_highZeroSum_phase_integrable hN q T eta),
    abelTransform_sub _ _ _ _ (psi_phase_integrable N (1 : Character q) eta)
      (identity_phase_integrable N eta)]
  ring

end LiuWang.Proof.PrincipalExpansion
