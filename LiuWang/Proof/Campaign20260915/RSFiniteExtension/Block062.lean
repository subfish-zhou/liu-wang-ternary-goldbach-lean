import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0622
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block062 : List ℕ := [14437, 14447, 14449, 14461, 14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653]

theorem complete_Block062 :
    ∀ p ∈ Finset.Ioc 14431 14653, p.Prime ↔ p ∈ primes_Block062 := by
  apply checked_of_primeSpan
  unfold primes_Block062
  apply primeSpan_cons (by norm_num) row_14437.1 gap_14437 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14447.1 gap_14447 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14449.1 gap_14449 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14461.1 gap_14461 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14479.1 gap_14479 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14489.1 gap_14489 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14503.1 gap_14503 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14519.1 gap_14519 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14533.1 gap_14533 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14537.1 gap_14537 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14543.1 gap_14543 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14549.1 gap_14549 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14551.1 gap_14551 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14557.1 gap_14557 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14561.1 gap_14561 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14563.1 gap_14563 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14591.1 gap_14591 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14593.1 gap_14593 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14621.1 gap_14621 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14627.1 gap_14627 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14629.1 gap_14629 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14633.1 gap_14633 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14639.1 gap_14639 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14653.1 gap_14653 (by norm_num)
  exact primeSpan_nil 14653

#print axioms reach_14653

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
