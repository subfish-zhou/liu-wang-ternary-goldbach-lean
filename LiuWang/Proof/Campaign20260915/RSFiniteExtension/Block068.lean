import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0682
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block068 : List ℕ := [15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919, 15923, 15937, 15959, 15971]

theorem complete_Block068 :
    ∀ p ∈ Finset.Ioc 15739 15971, p.Prime ↔ p ∈ primes_Block068 := by
  apply checked_of_primeSpan
  unfold primes_Block068
  apply primeSpan_cons (by norm_num) row_15749.1 gap_15749 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15761.1 gap_15761 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15767.1 gap_15767 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15773.1 gap_15773 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15787.1 gap_15787 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15791.1 gap_15791 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15797.1 gap_15797 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15803.1 gap_15803 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15809.1 gap_15809 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15817.1 gap_15817 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15823.1 gap_15823 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15859.1 gap_15859 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15877.1 gap_15877 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15881.1 gap_15881 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15887.1 gap_15887 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15889.1 gap_15889 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15901.1 gap_15901 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15907.1 gap_15907 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15913.1 gap_15913 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15919.1 gap_15919 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15923.1 gap_15923 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15937.1 gap_15937 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15959.1 gap_15959 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15971.1 gap_15971 (by norm_num)
  exact primeSpan_nil 15971

#print axioms reach_15971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
