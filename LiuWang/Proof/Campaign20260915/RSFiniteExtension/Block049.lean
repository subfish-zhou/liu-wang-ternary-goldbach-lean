import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0492
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block049 : List ℕ := [11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699]

theorem complete_Block049 :
    ∀ p ∈ Finset.Ioc 11443 11699, p.Prime ↔ p ∈ primes_Block049 := by
  apply checked_of_primeSpan
  unfold primes_Block049
  apply primeSpan_cons (by norm_num) row_11447.1 gap_11447 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11467.1 gap_11467 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11471.1 gap_11471 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11483.1 gap_11483 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11489.1 gap_11489 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11491.1 gap_11491 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11497.1 gap_11497 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11503.1 gap_11503 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11519.1 gap_11519 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11527.1 gap_11527 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11549.1 gap_11549 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11551.1 gap_11551 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11579.1 gap_11579 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11587.1 gap_11587 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11593.1 gap_11593 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11597.1 gap_11597 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11617.1 gap_11617 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11621.1 gap_11621 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11633.1 gap_11633 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11657.1 gap_11657 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11677.1 gap_11677 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11681.1 gap_11681 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11689.1 gap_11689 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11699.1 gap_11699 (by norm_num)
  exact primeSpan_nil 11699

#print axioms reach_11699

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
