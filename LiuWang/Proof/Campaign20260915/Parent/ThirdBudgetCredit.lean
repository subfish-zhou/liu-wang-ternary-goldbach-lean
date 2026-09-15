import LiuWang.Proof.Campaign20260915.ThirdDomainTail.Main
import LiuWang.Proof.Campaign20260915.Totient.M6
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.RealTail
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.Assembly
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Parent.RealCredit

def middleEndpoint (N q : ℕ) [NeZero q] : ℝ :=
  (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
    countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1

def middleIntegral (N q : ℕ) [NeZero q] : ℝ :=
  (8 * N * Real.sqrt q / q.totient) *
    ∫ y in lowHeight..middleHeight N q,
      y ^ (-3 / 2 : ℝ) * countIntegral q (0.001 * N) y (59 / 60) 1

/-- Three actual unpaid terms after the proved Abel credit; no zero-tail assumption. -/
def unpaidRemainder (N q : ℕ) [NeZero q] : ℝ :=
  middleEndpoint N q + middleIntegral N q + sourceM5 N q

theorem sigma6_M6_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hhigh : (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hlocal : ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    sigma6 N q ≤
      (0.000120006 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
        sourceM5 N q := by
  have h := ThirdDomainTail.sigma6_original_reduction_without_cumulative_real_tail
    hN hq hq1 hhigh htotient (Totient.third_sourceNu_le_sixth hN hq hq1) hlocal
  have h6 := mul_le_mul_of_nonneg_left
    (M6Certificate.m6OriginalScalar_le (sourceL N) (sourceL_ge_3100 hN))
    (show 0 ≤ (N : ℝ) / sourceL N from
      div_nonneg (Nat.cast_nonneg N) (by linarith [sourceL_ge_3100 hN]))
  ring_nf at h h6 ⊢
  linarith only [h, h6]


theorem S_and_primeS_original_payments {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) {eta : ℝ}
    (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hlow : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha)
    (hhigh : (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60))
    {e : Option ((_chi : Character q) × ℂ)} (hloc : Source521523.LocalC1Data q e)
    (hlocal : ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖S N (rationalCenter a q + eta)‖ ≤
        (0.370600686001 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          unpaidRemainder N q ∧
      ‖primeS N (rationalCenter a q + eta)‖ ≤
        (0.370600686002 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          unpaidRemainder N q := by
  have hS := S_principal_and_error_paid hN hi hq hq1 heta
  have h4 := Source521523.equation_5_27_original_conditional hN hq.le hq1
    htotient hlow hloc
  have h5 := equation_5_31_actual_count hN hq1
  have h6 := sigma6_M6_paid hN hq.le hq1 hhigh htotient hlocal
  have hprime := primeS_M3_fixed hN hi hq hq1 heta
  have hprincipal := principal_bound_paid hN hq.le
  dsimp only [unpaidRemainder, middleEndpoint, middleIntegral]
  ring_nf at hS h4 h5 h6 hprime hprincipal ⊢
  constructor
  · linarith only [hS, h4, h5, h6]
  · linarith only [hprime, hprincipal, h4, h5, h6]

theorem original_payments_same_witness {N : ℕ} {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (ha : alpha ∈ M3 N)
    (htotient : ∀ q : ℕ, sourceP N < (q : ℝ) → (q : ℝ) ≤ sourceP1 N →
      (q : ℝ) / q.totient ≤ sourceNu q)
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
        (0.370600686001 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          unpaidRemainder N q ∧
      ‖primeS N alpha‖ ≤
        (0.370600686002 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          unpaidRemainder N q := by
  obtain ⟨q, a, eta, hq0, hq1, hi, he, heta⟩ := LiuWang.Proof.ArcGeometry.M3_eta_range ha
  have hq := LiuWang.Proof.ArcGeometry.sourceIndex_den_pos hi
  let : NeZero q := ⟨hq.ne'⟩
  rw [approximationRadius_eq (exp_2000_le_of_exp_3100_le hN) hq] at heta
  obtain ⟨e, heLocal⟩ := hloc q hq0 hq1
  refine ⟨q, a, eta, hq, hq0, hq1, hi, he, heta, ?_⟩
  rw [he]
  exact S_and_primeS_original_payments hN hi hq0 hq1 heta
    (htotient q hq0 hq1) (hlow q hq0 hq1) (hhigh q hq0 hq1)
    heLocal (hlocal q hq0 hq1)

#check @sigma6_M6_paid
#check @original_payments_same_witness
#print axioms sigma6_M6_paid
#print axioms S_and_primeS_original_payments
#print axioms original_payments_same_witness

end LiuWang.Proof.Campaign20260915.Parent.RealCredit
