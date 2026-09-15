import LiuWang.Proof.Campaign20260915.SmallConductors.LocalC1
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.Assembly

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SmallConductors

theorem equation_5_27_local_region_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha) :
    SourceRoute.ThirdArc.sigma4 N q ≤ (0.36938 : ℝ) * N / sourceL N := by
  obtain ⟨e, he⟩ := localC1Data_exists hN hq
  exact Source521523.equation_5_27_original_conditional hN hq hq1 htotient hdensity he

#print axioms equation_5_27_local_region_paid

end LiuWang.Proof.Campaign20260915.SmallConductors
