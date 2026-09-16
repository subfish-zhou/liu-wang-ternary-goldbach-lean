import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0372
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block037 : List ℕ := [8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971]

theorem complete_Block037 :
    ∀ p ∈ Finset.Ioc 8753 8971, p.Prime ↔ p ∈ primes_Block037 := by
  apply checked_of_primeSpan
  unfold primes_Block037
  apply primeSpan_cons (by norm_num) row_8761.1 gap_8761 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8779.1 gap_8779 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8783.1 gap_8783 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8803.1 gap_8803 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8807.1 gap_8807 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8819.1 gap_8819 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8821.1 gap_8821 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8831.1 gap_8831 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8837.1 gap_8837 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8839.1 gap_8839 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8849.1 gap_8849 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8861.1 gap_8861 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8863.1 gap_8863 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8867.1 gap_8867 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8887.1 gap_8887 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8893.1 gap_8893 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8923.1 gap_8923 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8929.1 gap_8929 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8933.1 gap_8933 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8941.1 gap_8941 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8951.1 gap_8951 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8963.1 gap_8963 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8969.1 gap_8969 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8971.1 gap_8971 (by norm_num)
  exact primeSpan_nil 8971

#print axioms reach_8971

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
