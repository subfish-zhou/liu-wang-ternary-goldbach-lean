import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0282
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block028 : List ℕ := [6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997]

theorem complete_Block028 :
    ∀ p ∈ Finset.Ioc 6803 6997, p.Prime ↔ p ∈ primes_Block028 := by
  apply checked_of_primeSpan
  unfold primes_Block028
  apply primeSpan_cons (by norm_num) row_6823.1 gap_6823 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6827.1 gap_6827 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6829.1 gap_6829 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6833.1 gap_6833 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6841.1 gap_6841 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6857.1 gap_6857 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6863.1 gap_6863 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6869.1 gap_6869 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6871.1 gap_6871 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6883.1 gap_6883 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6899.1 gap_6899 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6907.1 gap_6907 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6911.1 gap_6911 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6917.1 gap_6917 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6947.1 gap_6947 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6949.1 gap_6949 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6959.1 gap_6959 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6961.1 gap_6961 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6967.1 gap_6967 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6971.1 gap_6971 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6977.1 gap_6977 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6983.1 gap_6983 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6991.1 gap_6991 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6997.1 gap_6997 (by norm_num)
  exact primeSpan_nil 6997

#print axioms reach_6997

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
