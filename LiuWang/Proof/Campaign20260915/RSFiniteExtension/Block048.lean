import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0482
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block048 : List ℕ := [11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443]

theorem complete_Block048 :
    ∀ p ∈ Finset.Ioc 11197 11443, p.Prime ↔ p ∈ primes_Block048 := by
  apply checked_of_primeSpan
  unfold primes_Block048
  apply primeSpan_cons (by norm_num) row_11213.1 gap_11213 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11239.1 gap_11239 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11243.1 gap_11243 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11251.1 gap_11251 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11257.1 gap_11257 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11261.1 gap_11261 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11273.1 gap_11273 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11279.1 gap_11279 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11287.1 gap_11287 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11299.1 gap_11299 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11311.1 gap_11311 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11317.1 gap_11317 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11321.1 gap_11321 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11329.1 gap_11329 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11351.1 gap_11351 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11353.1 gap_11353 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11369.1 gap_11369 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11383.1 gap_11383 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11393.1 gap_11393 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11399.1 gap_11399 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11411.1 gap_11411 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11423.1 gap_11423 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11437.1 gap_11437 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11443.1 gap_11443 (by norm_num)
  exact primeSpan_nil 11443

#print axioms reach_11443

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
