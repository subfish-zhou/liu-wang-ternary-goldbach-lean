import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.PrimedIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

theorem originalPrimedBill_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha) :
    originalPrimedBill N q ≤
      (0.00365 + 0.24981 + 0.00003 + 0.00003 : ℝ) * N / sourceL N := by
  rw [original_finite_bill_decomposition hN hq]
  have hb := equation_5_23_original hN hq1
  have hd := Source524.equation_5_24_original_contribution hN hq hq1 htotient hdensity
  have hs := Source525526.equation_5_25_original hN hq hq1 htotient
  have ht := Source525526.equation_5_26_original hN hq hq1 htotient
  simp only [div_eq_mul_inv] at hb hd hs ht ⊢
  nlinarith only [hb, hd, hs, ht]

theorem equation_5_21_extraction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e) :
    sigma4 N q ≤ (0.11585 : ℝ) * N / sourceL N + primedSigma4 N q e := by
  rw [sigma4_exact_local_split hN hq1 hloc]
  linarith only [selectedBill_paid hN hq htotient hloc]

theorem equation_5_27_original_conditional {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha)
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e) :
    sigma4 N q ≤ (0.36938 : ℝ) * N / sourceL N := by
  have h := equation_5_21_extraction hN hq hq1 htotient hloc
  have hr := primedSigma4_le_original_bill hN hq hloc
  have hp := originalPrimedBill_paid hN hq hq1 htotient hdensity
  have hL := sourceL_ge_3100 hN
  have hnon : 0 ≤ (N : ℝ) * (sourceL N)⁻¹ := by positivity
  simp only [div_eq_mul_inv] at h hp ⊢
  nlinarith only [h, hr, hp, hnon]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
