import LiuWang.Proof.Campaign20260915.ThirdBudgets.Assembly
import LiuWang.Proof.Campaign20260915.ThirdBudgets.EndpointTable

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

def middleEndpointDensity (N q : ℕ) [NeZero q] : ℝ :=
  (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
    countIntegral q (0.001 * N) (middleHeight N q) (59 / 60)
      (1 - 0.478 / Real.log ((q : ℝ) * middleHeight N q))

def remainingAfterEndpointTable (N q : ℕ) [NeZero q] : ℝ :=
  middleEndpointDensity N q + middleIntegral N q + sourceM5 N q + sourceHighRealTail N q

theorem unpaidRemainder_table_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    unpaidRemainder N q ≤
      remainingAfterEndpointTable N q + 0.000001 * (N : ℝ) / sourceL N := by
  have h := middle_endpoint_density_remainder hN hq hq1 htotient hnu
  change middleEndpoint N q ≤ middleEndpointDensity N q + _ at h
  unfold unpaidRemainder remainingAfterEndpointTable
  linarith only [h]

theorem endpoint_table_payments_same_witness {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M3 N)
    (htotient : ∀ q : ℕ, sourceP N < (q : ℝ) → (q : ℝ) ≤ sourceP1 N →
      (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : ∀ q : ℕ, sourceP N < (q : ℝ) → (q : ℝ) ≤ sourceP1 N →
      sourceNu q ≤ sourceNu (sourceL N ^ 6))
    (hlow : ∀ (q : ℕ) [NeZero q], sourceP N < (q : ℝ) →
      (q : ℝ) ≤ sourceP1 N →
      ∀ beta ∈ Set.Icc (59 / 60 : ℝ)
        (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q beta (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) beta)
    (hhigh : ∀ (q : ℕ) [NeZero q], sourceP N < (q : ℝ) →
      (q : ℝ) ≤ sourceP1 N →
      (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
        sourceDensity q (sourceT N) (59 / 60))
    (hloc : ∀ (q : ℕ) [NeZero q], sourceP N < (q : ℝ) →
      (q : ℝ) ≤ sourceP1 N →
      ∃ e : Option ((_chi : Character q) × ℂ), Source521523.LocalC1Data q e)
    (hlocal : ∀ (q : ℕ) [NeZero q], sourceP N < (q : ℝ) →
      (q : ℝ) ≤ sourceP1 N →
      ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ∃ (q a : ℕ) (eta : ℝ) (hq : 0 < q),
      let : NeZero q := ⟨hq.ne'⟩
      sourceL N ^ 3 < (q : ℝ) ∧ (q : ℝ) ≤ sourceL N ^ 6 ∧
      sourceIndex a q ∧ alpha = rationalCenter a q + eta ∧
      |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N) ∧
      ‖S N alpha‖ ≤
        (0.370601686001 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          remainingAfterEndpointTable N q ∧
      ‖primeS N alpha‖ ≤
        (0.370601686002 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          remainingAfterEndpointTable N q := by
  obtain ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, hS, hprime⟩ :=
    original_payments_same_witness hN ha htotient hnu hlow hhigh hloc hlocal
  let : NeZero q := ⟨hq.ne'⟩
  have hr := unpaidRemainder_table_paid hN hq0.le hq1
    (htotient q hq0 hq1) (hnu q hq0 hq1)
  refine ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, ?_, ?_⟩
  · ring_nf at hS hr ⊢
    linarith only [hS, hr]
  · ring_nf at hprime hr ⊢
    linarith only [hprime, hr]

#print axioms unpaidRemainder_table_paid
#print axioms endpoint_table_payments_same_witness

end LiuWang.Proof.Campaign20260915.ThirdBudgets
