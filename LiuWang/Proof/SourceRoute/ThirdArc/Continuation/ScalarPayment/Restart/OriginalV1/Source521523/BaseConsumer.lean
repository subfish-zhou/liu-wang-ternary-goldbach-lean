import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.OriginalCount
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowAssembly

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

theorem original_base_integral_cancellation {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-1 / 2 : ℝ) +
      (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ), betaKernel N alpha) =
        (N : ℝ) ^ (-1 / 60 : ℝ) := by
  rw [integral_betaKernel (Nat.cast_pos.mpr hN)]
  norm_num

theorem original_low_beta_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      lowCoefficient (1 / 2) * (q.totient * originalCountFactor q) *
        ((N : ℝ) ^ (-1 / 60 : ℝ) - (N : ℝ) ^ (-1 / 2 : ℝ)) := by
  have hn := natCast_pos_of_exp_le hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  calc
    _ ≤ ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
        (lowCoefficient (1 / 2) * (q.totient * originalCountFactor q)) *
          betaKernel N alpha := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (family_low_integrable q _ hn le_rfl (by norm_num))
        (((betaKernel_continuous hn).intervalIntegrable _ _).const_mul _)
      intro alpha halpha
      have hc := original_count_family q halpha.1
      have hw := lowCoefficient_antitone (by norm_num : (0 : ℝ) < 1 / 2) halpha.1
      have h := mul_le_mul hw hc (Nat.cast_nonneg _) (lowCoefficient_nonneg (by norm_num))
      have hk : 0 ≤ betaKernel N alpha :=
        mul_nonneg (Real.rpow_nonneg hn.le _) (Real.log_nonneg hN1)
      have h := mul_le_mul_of_nonneg_left h hk
      nlinarith only [h]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_betaKernel hn]
      norm_num

theorem lowBetaBill_le_original_scalar {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    lowBetaBill N q ≤
      (N : ℝ) * Real.sqrt q * lowCoefficient (1 / 2) *
        originalCountFactor q * (N : ℝ) ^ (-1 / 60 : ℝ) := by
  have hf : (q.totient : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))).ne'
  have hb := mul_le_mul_of_nonneg_left (original_count_family q (alpha := 1 / 2) le_rfl)
    (mul_nonneg (lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 1 / 2))
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-1 / 2 : ℝ)))
  have hi := original_low_beta_integral (q := q) hN
  have h := mul_le_mul_of_nonneg_left (add_le_add hb hi)
    (show 0 ≤ (N : ℝ) * Real.sqrt q / q.totient by positivity)
  apply h.trans_eq
  field_simp
  ring

theorem equation_5_23_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    lowBetaBill N q ≤ (0.00365 : ℝ) * N / sourceL N :=
  (lowBetaBill_le_original_scalar hN).trans (original_base_scalar_paid hN hq1)

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
