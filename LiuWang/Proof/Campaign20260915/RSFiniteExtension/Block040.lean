import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0402
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block040 : List ℕ := [9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623]

theorem complete_Block040 :
    ∀ p ∈ Finset.Ioc 9413 9623, p.Prime ↔ p ∈ primes_Block040 := by
  apply checked_of_primeSpan
  unfold primes_Block040
  apply primeSpan_cons (by norm_num) row_9419.1 gap_9419 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9421.1 gap_9421 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9431.1 gap_9431 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9433.1 gap_9433 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9437.1 gap_9437 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9439.1 gap_9439 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9461.1 gap_9461 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9463.1 gap_9463 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9467.1 gap_9467 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9473.1 gap_9473 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9479.1 gap_9479 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9491.1 gap_9491 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9497.1 gap_9497 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9511.1 gap_9511 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9521.1 gap_9521 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9533.1 gap_9533 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9539.1 gap_9539 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9547.1 gap_9547 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9551.1 gap_9551 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9587.1 gap_9587 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9601.1 gap_9601 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9613.1 gap_9613 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9619.1 gap_9619 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9623.1 gap_9623 (by norm_num)
  exact primeSpan_nil 9623

#print axioms reach_9623

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
