import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.CountFubini
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TablePayments
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.LogSubstitution

/-! Source coefficients and three original height windows, with unpaid density integrals explicit. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

theorem original_middle_count_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (∫ alpha in (59 / 60 : ℝ)..1, betaKernel (0.001 * N) alpha *
        densityBand q alpha lowHeight (middleHeight N q) (1 / 2)) ≤
      (1 / Real.sqrt (middleHeight N q)) *
          countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 +
        (1 / 2 : ℝ) * ∫ y in lowHeight..middleHeight N q,
          y ^ (-3 / 2 : ℝ) * countIntegral q (0.001 * N) y (59 / 60) 1 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have huv := (original_height_order hn hq1).1
  have h := densityBand_integral_le_counts q (a := 59 / 60) (b := 1)
    (original_middle_base_ge_one hN)
    (by norm_num) (by norm_num) lowHeight_pos huv (p := 1 / 2) (by norm_num)
  simp only [heightKernel, show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    Real.rpow_neg (lowHeight_pos.trans_le huv).le, ← Real.sqrt_eq_rpow,
    mul_assoc, intervalIntegral.integral_const_mul] at h
  simpa only [one_div] using h

theorem original_high_count_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (∫ alpha in (59 / 60 : ℝ)..1, betaKernel N alpha *
        densityBand q alpha (middleHeight N q) (sourceT N) 1) ≤
      (1 / sourceT N) * countIntegral q N (sourceT N) (59 / 60) 1 +
        ∫ y in middleHeight N q..sourceT N,
          y ^ (-2 : ℝ) * countIntegral q N y (59 / 60) 1 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hh := original_height_order hn hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have h := densityBand_integral_le_counts q (a := 59 / 60) (b := 1) hX
    (by norm_num) (by norm_num)
    (lowHeight_pos.trans_le hh.1) hh.2 (p := 1) (by norm_num)
  simpa only [heightKernel, show -(1 : ℝ) - 1 = -2 by norm_num,
    Real.rpow_neg_one, one_div, one_mul] using h

theorem original_low_table_bill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
        (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * lowHeight))..
            (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)),
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      ((N : ℝ) * Real.sqrt q / q.totient) *
        (lowCoefficient (59 / 60) * threeRowPrice N ((q : ℝ) * lowHeight) 0.2067) :=
  mul_le_mul_of_nonneg_left (M3_low_three_row_integral_paid hN hq) (by positivity)

theorem original_middle_endpoint_table_bill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 ≤
      (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60)
          (1 - 0.478 / Real.log ((q : ℝ) * middleHeight N q)) +
      (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        threeRowPrice (0.001 * N) ((q : ℝ) * middleHeight N q) 0 := by
  have h := mul_le_mul_of_nonneg_left (original_middle_endpoint_split_paid hN hq hq1)
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q) by positivity)
  simpa only [mul_add] using h

theorem original_high_endpoint_table_bill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (5 * N * Real.sqrt q / q.totient / sourceT N) *
        countIntegral q N (sourceT N) (59 / 60) 1 ≤
      (5 * N * Real.sqrt q / q.totient / sourceT N) *
        countIntegral q N (sourceT N) (59 / 60)
          (1 - 0.478 / Real.log ((q : ℝ) * sourceT N)) +
      (5 * N * Real.sqrt q / q.totient / sourceT N) *
        threeRowPrice N ((q : ℝ) * sourceT N) 0 := by
  have hT : 0 ≤ sourceT N := pow_nonneg (sourceL_pos (exp_2000_le_of_exp_3100_le hN)).le _
  have h := mul_le_mul_of_nonneg_left (original_high_endpoint_split_paid hN hq hq1)
    (show 0 ≤ 5 * N * Real.sqrt q / q.totient / sourceT N by positivity)
  simpa only [mul_add] using h

theorem original_middle_height_table_bill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y : ℝ} (hy : y ∈ Set.Icc lowHeight (middleHeight N q)) :
    (8 * N * Real.sqrt q / q.totient) * y ^ (-3 / 2 : ℝ) *
        countIntegral q (0.001 * N) y (59 / 60) 1 ≤
      (8 * N * Real.sqrt q / q.totient) * y ^ (-3 / 2 : ℝ) *
        (countIntegral q (0.001 * N) y (59 / 60)
          (1 - 0.478 / Real.log ((q : ℝ) * y)) +
          threeRowPrice (0.001 * N) ((q : ℝ) * y) 0) :=
  mul_le_mul_of_nonneg_left
    (M3_countIntegral_split_paid hN hq (original_middle_base_ge_one hN) hy.1)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (lowHeight_pos.trans_le hy.1).le _))

theorem original_high_height_table_bill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {y : ℝ} (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N)) :
    (5 * N * Real.sqrt q / q.totient) * y ^ (-2 : ℝ) *
        countIntegral q N y (59 / 60) 1 ≤
      (5 * N * Real.sqrt q / q.totient) * y ^ (-2 : ℝ) *
        (countIntegral q N y (59 / 60) (1 - 0.478 / Real.log ((q : ℝ) * y)) +
          threeRowPrice N ((q : ℝ) * y) 0) := by
  have hlow := ((original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1).trans hy.1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  exact mul_le_mul_of_nonneg_left (M3_countIntegral_split_paid hN hq hX hlow)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (lowHeight_pos.trans_le hlow).le _))

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
