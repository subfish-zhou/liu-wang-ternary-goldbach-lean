import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowBetaScalar
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowCount

/-! Payment of the actual endpoint and first beta integral in original (5.22)/(5.23). -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

def lowBetaBill (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    (lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) * familyCount q (1 / 2) lowHeight +
      ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight)

theorem low_beta_integral_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      lowCoefficient (1 / 2) * (q.totient * (10004 * Real.log q + 76100)) *
        ((N : ℝ) ^ (-1 / 60 : ℝ) - (N : ℝ) ^ (-1 / 2 : ℝ)) := by
  have hn := natCast_pos_of_exp_le hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  calc
    _ ≤ ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
        (lowCoefficient (1 / 2) * (q.totient * (10004 * Real.log q + 76100))) *
          betaKernel N alpha := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (family_low_integrable q _ hn le_rfl (by norm_num))
        (((betaKernel_continuous hn).intervalIntegrable _ _).const_mul _)
      intro alpha halpha
      have hc := low_count_family q (by linarith [halpha.1] : 0 ≤ alpha)
      have hw := lowCoefficient_antitone (by norm_num : (0 : ℝ) < 1 / 2) halpha.1
      have h := mul_le_mul hw hc (Nat.cast_nonneg _) (lowCoefficient_nonneg (by norm_num))
      have hk : 0 ≤ betaKernel N alpha :=
        mul_nonneg (Real.rpow_nonneg hn.le _) (Real.log_nonneg hN1)
      have h := mul_le_mul_of_nonneg_left h hk
      nlinarith only [h]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_betaKernel hn]
      norm_num

theorem low_beta_count_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lowBetaBill N q ≤
      (N : ℝ) * Real.sqrt q * lowCoefficient (1 / 2) *
        (10004 * Real.log q + 76100) * (N : ℝ) ^ (-1 / 60 : ℝ) := by
  have hf : (q.totient : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))).ne'
  have hbase := mul_le_mul_of_nonneg_left (low_count_family q (alpha := 1 / 2) (by norm_num))
    (mul_nonneg (lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 1 / 2))
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-1 / 2 : ℝ)))
  have hi := low_beta_integral_count_bound (q := q) hN
  have h := mul_le_mul_of_nonneg_left (add_le_add hbase hi)
    (show 0 ≤ (N : ℝ) * Real.sqrt q / q.totient by positivity)
  apply h.trans_eq
  field_simp
  ring

theorem equation_5_23_stronger {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    lowBetaBill N q ≤ 0.00365 * (N : ℝ) / sourceL N :=
  (low_beta_count_envelope hN).trans (low_beta_scalar_paid hN hq1)

theorem equation_5_23 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (_hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
        (2 * (1 - (0.001 : ℝ) ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (-1 / 2 : ℝ) *
            familyCount q (1 / 2) lowHeight +
          ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      0.00365 * (N : ℝ) / sourceL N := by
  have h := equation_5_23_stronger hN hq1
  convert h using 1
  unfold lowBetaBill lowCoefficient
  ring

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
