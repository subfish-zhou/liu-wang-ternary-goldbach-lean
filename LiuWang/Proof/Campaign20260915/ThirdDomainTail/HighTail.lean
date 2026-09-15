import LiuWang.Proof.Campaign20260915.ThirdDomainTail.NonrealFubini
import LiuWang.Proof.Campaign20260915.ThirdDomainTail.RealCredit

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem sourceHighRealTail_le_abel_credit {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sourceHighRealTail N q ≤
      (5 * N * Real.sqrt q / q.totient) *
        ((middleHeight N q)⁻¹ * countIntegral q N 0 (59 / 60) 1) :=
  sourceHighRealTail_le_credit_without_local hN hq hq1

theorem sigma6_original_reduction_without_cumulative_real_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hhigh : (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6))
    (hlocal : ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    sigma6 N q ≤ (0.00012 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
      sourceM5 N q + (N : ℝ) / sourceL N * m6OriginalScalar (sourceL N) := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have habel := densityBand_integral_real_credit q hX
    (a := 59 / 60) (b := 1) (p := 1) (by norm_num) (by norm_num)
    (lowHeight_pos.trans_le hh.1) hh.2 (by norm_num)
  simp only [Real.rpow_neg_one, heightKernel, one_mul,
    show -(1 : ℝ) - 1 = -2 by norm_num] at habel
  have hscaled := mul_le_mul_of_nonneg_left habel
    (show 0 ≤ 5 * N * Real.sqrt q / q.totient by positivity)
  have hlow := sigma6_low_beta_paid hN hq1
  have hend := equation_5_41_actual_count hN hq hq1 hhigh
  have hsplit := equation_5_42_with_real_tail hN hq hq1 hlocal
  have htail := sourceHighRealTail_le_abel_credit hN hq hq1
  have hm6 := equation_5_44_original_integral hN hq hq1 htotient hnu
  simp only [div_eq_mul_inv] at hscaled hlow hend hsplit htail hm6 ⊢
  nlinarith only [hscaled, hlow, hend, hsplit, htail, hm6]

#print axioms sourceHighRealTail_le_abel_credit
#print axioms sigma6_original_reduction_without_cumulative_real_tail

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
