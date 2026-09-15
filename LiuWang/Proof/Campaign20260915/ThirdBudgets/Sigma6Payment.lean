import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5ActualPayment
import LiuWang.Proof.Campaign20260915.ThirdDomainTail.HighTail
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Payment

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem sigma6_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6))
    (hlocal : ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    sigma6 N q ≤ (0.000190006 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hcut := (sourceCutoff_order hN hq (hh.1.trans hh.2) (d := 0.478) (e := 0.478)
    (by norm_num) le_rfl le_rfl).1
  have hhigh := hdensity (sourceT N) ⟨high_endpoint_source_domain hN hq1, le_rfl⟩
    (59 / 60) ⟨le_rfl, hcut⟩
  have h := ThirdDomainTail.sigma6_original_reduction_without_cumulative_real_tail
    hN hq hq1 hhigh htotient hnu hlocal
  have h5 := sourceM5_original_paid hN hq hq1 hdensity htotient hnu
  have h6 := mul_le_mul_of_nonneg_left
    (M6Certificate.m6OriginalScalar_le (sourceL N) (sourceL_ge_3100 hN))
    (div_nonneg (Nat.cast_nonneg N) (sourceL_pos (exp_2000_le_of_exp_3100_le hN)).le)
  ring_nf at h h5 h6 ⊢
  linarith only [h, h5, h6]

#print axioms sigma6_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
