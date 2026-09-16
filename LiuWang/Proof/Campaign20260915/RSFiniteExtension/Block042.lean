import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0422
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block042 : List ℕ := [9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069]

theorem complete_Block042 :
    ∀ p ∈ Finset.Ioc 9829 10069, p.Prime ↔ p ∈ primes_Block042 := by
  apply checked_of_primeSpan
  unfold primes_Block042
  apply primeSpan_cons (by norm_num) row_9833.1 gap_9833 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9839.1 gap_9839 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9851.1 gap_9851 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9857.1 gap_9857 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9859.1 gap_9859 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9871.1 gap_9871 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9883.1 gap_9883 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9887.1 gap_9887 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9901.1 gap_9901 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9907.1 gap_9907 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9923.1 gap_9923 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9929.1 gap_9929 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9931.1 gap_9931 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9941.1 gap_9941 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9949.1 gap_9949 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9967.1 gap_9967 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9973.1 gap_9973 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10007.1 gap_10007 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10009.1 gap_10009 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10037.1 gap_10037 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10039.1 gap_10039 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10061.1 gap_10061 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10067.1 gap_10067 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10069.1 gap_10069 (by norm_num)
  exact primeSpan_nil 10069

#print axioms reach_10069

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
