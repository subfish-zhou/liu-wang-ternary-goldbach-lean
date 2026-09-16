import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0432
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block043 : List ℕ := [10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271]

theorem complete_Block043 :
    ∀ p ∈ Finset.Ioc 10069 10271, p.Prime ↔ p ∈ primes_Block043 := by
  apply checked_of_primeSpan
  unfold primes_Block043
  apply primeSpan_cons (by norm_num) row_10079.1 gap_10079 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10091.1 gap_10091 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10093.1 gap_10093 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10099.1 gap_10099 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10103.1 gap_10103 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10111.1 gap_10111 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10133.1 gap_10133 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10139.1 gap_10139 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10141.1 gap_10141 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10151.1 gap_10151 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10159.1 gap_10159 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10163.1 gap_10163 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10169.1 gap_10169 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10177.1 gap_10177 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10181.1 gap_10181 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10193.1 gap_10193 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10211.1 gap_10211 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10223.1 gap_10223 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10243.1 gap_10243 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10247.1 gap_10247 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10253.1 gap_10253 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10259.1 gap_10259 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10267.1 gap_10267 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10271.1 gap_10271 (by norm_num)
  exact primeSpan_nil 10271

#print axioms reach_10271

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
