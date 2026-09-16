import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0642
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block064 : List ℕ := [14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929, 14939, 14947, 14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101]

theorem complete_Block064 :
    ∀ p ∈ Finset.Ioc 14851 15101, p.Prime ↔ p ∈ primes_Block064 := by
  apply checked_of_primeSpan
  unfold primes_Block064
  apply primeSpan_cons (by norm_num) row_14867.1 gap_14867 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14869.1 gap_14869 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14879.1 gap_14879 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14887.1 gap_14887 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14891.1 gap_14891 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14897.1 gap_14897 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14923.1 gap_14923 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14929.1 gap_14929 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14939.1 gap_14939 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14947.1 gap_14947 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14951.1 gap_14951 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14957.1 gap_14957 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14969.1 gap_14969 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14983.1 gap_14983 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15013.1 gap_15013 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15017.1 gap_15017 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15031.1 gap_15031 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15053.1 gap_15053 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15061.1 gap_15061 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15073.1 gap_15073 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15077.1 gap_15077 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15083.1 gap_15083 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15091.1 gap_15091 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15101.1 gap_15101 (by norm_num)
  exact primeSpan_nil 15101

#print axioms reach_15101

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
