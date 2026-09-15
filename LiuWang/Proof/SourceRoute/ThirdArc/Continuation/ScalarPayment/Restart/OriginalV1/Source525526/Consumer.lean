import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Count

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526

theorem lowStripBill_le_original_weight {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    lowStripBill N q ≤ ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (59 / 60) * (14000 *
        Real.exp (-0.2067 * sourceL N / Real.log ((q : ℝ) * lowHeight)))) := by
  have hx := natCast_pos_of_exp_le hN
  have hc := lowCoefficient_nonneg (by norm_num : (0 : ℝ) < 59 / 60)
  have he : (N : ℝ) ^ (-0.2067 / Real.log ((q : ℝ) * lowHeight)) =
      Real.exp (-0.2067 * sourceL N / Real.log ((q : ℝ) * lowHeight)) := by
    rw [Real.rpow_def_of_pos hx, sourceL]
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_left (original_low_0478_subinterval hN hq)
    (show 0 ≤ (N : ℝ) * Real.sqrt q / q.totient by positivity)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← he]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.rpow_nonneg hx.le _)) (by norm_num)) hc

theorem equation_5_25_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    lowStripBill N q ≤ (3 / 100000 : ℝ) * (N : ℝ) / sourceL N :=
  (lowStripBill_le_original_weight hN hq).trans (original_weight525_paid hN hq hq1 htotient)

theorem originalLastBill_le_original_weight {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    originalLastBill N q ≤ ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (59 / 60) * (2 *
        Real.exp (-0.10367089 * sourceL N / Real.log ((q : ℝ) * lowHeight)))) :=
  mul_le_mul_of_nonneg_left (original_last_integral_bound hN hq) (by positivity)

theorem equation_5_26_original {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q) :
    originalLastBill N q ≤ (3 / 100000 : ℝ) * (N : ℝ) / sourceL N :=
  (originalLastBill_le_original_weight hN hq).trans (original_weight526_paid hN hq hq1 htotient)

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526
