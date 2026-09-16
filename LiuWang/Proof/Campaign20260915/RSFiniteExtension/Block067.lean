import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0672
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block067 : List ℕ := [15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607, 15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739]

theorem complete_Block067 :
    ∀ p ∈ Finset.Ioc 15527 15739, p.Prime ↔ p ∈ primes_Block067 := by
  apply checked_of_primeSpan
  unfold primes_Block067
  apply primeSpan_cons (by norm_num) row_15541.1 gap_15541 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15551.1 gap_15551 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15559.1 gap_15559 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15569.1 gap_15569 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15581.1 gap_15581 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15583.1 gap_15583 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15601.1 gap_15601 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15607.1 gap_15607 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15619.1 gap_15619 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15629.1 gap_15629 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15641.1 gap_15641 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15643.1 gap_15643 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15647.1 gap_15647 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15649.1 gap_15649 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15661.1 gap_15661 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15667.1 gap_15667 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15671.1 gap_15671 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15679.1 gap_15679 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15683.1 gap_15683 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15727.1 gap_15727 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15731.1 gap_15731 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15733.1 gap_15733 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15737.1 gap_15737 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15739.1 gap_15739 (by norm_num)
  exact primeSpan_nil 15739

#print axioms reach_15739

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
