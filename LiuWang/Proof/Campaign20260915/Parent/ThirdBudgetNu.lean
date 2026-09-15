import LiuWang.Proof.Campaign20260915.ThirdBudgets.PaidAssembly
import LiuWang.Proof.Campaign20260915.Totient.M6

/-! Parent integration removes only the proved nu monotonicity input.
The original totient, density, local-region inputs and real-tail remainder remain.
-/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Parent

theorem endpoint_table_payments_same_witness {N : ℕ} {alpha : ℝ}
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
        (0.370601686001 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          ThirdBudgets.remainingAfterEndpointTable N q ∧
      ‖primeS N alpha‖ ≤
        (0.370601686002 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
          ThirdBudgets.remainingAfterEndpointTable N q :=
  ThirdBudgets.endpoint_table_payments_same_witness hN ha htotient
    (fun _ hq hq1 => Totient.third_sourceNu_le_sixth hN hq.le hq1)
    hlow hhigh hloc hlocal

#check @endpoint_table_payments_same_witness
#print axioms endpoint_table_payments_same_witness

end LiuWang.Proof.Campaign20260915.Parent
