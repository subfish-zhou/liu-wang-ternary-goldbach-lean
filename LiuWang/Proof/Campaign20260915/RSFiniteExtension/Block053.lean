import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0532
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block053 : List ℕ := [12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553]

theorem complete_Block053 :
    ∀ p ∈ Finset.Ioc 12373 12553, p.Prime ↔ p ∈ primes_Block053 := by
  apply checked_of_primeSpan
  unfold primes_Block053
  apply primeSpan_cons (by norm_num) row_12377.1 gap_12377 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12379.1 gap_12379 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12391.1 gap_12391 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12401.1 gap_12401 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12409.1 gap_12409 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12413.1 gap_12413 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12421.1 gap_12421 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12433.1 gap_12433 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12437.1 gap_12437 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12451.1 gap_12451 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12457.1 gap_12457 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12473.1 gap_12473 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12479.1 gap_12479 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12487.1 gap_12487 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12491.1 gap_12491 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12497.1 gap_12497 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12503.1 gap_12503 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12511.1 gap_12511 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12517.1 gap_12517 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12527.1 gap_12527 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12539.1 gap_12539 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12541.1 gap_12541 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12547.1 gap_12547 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12553.1 gap_12553 (by norm_num)
  exact primeSpan_nil 12553

#print axioms reach_12553

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
