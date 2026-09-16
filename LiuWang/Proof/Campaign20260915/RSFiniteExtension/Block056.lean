import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0562
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block056 : List ℕ := [13003, 13007, 13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177, 13183, 13187, 13217, 13219]

theorem complete_Block056 :
    ∀ p ∈ Finset.Ioc 13001 13219, p.Prime ↔ p ∈ primes_Block056 := by
  apply checked_of_primeSpan
  unfold primes_Block056
  apply primeSpan_cons (by norm_num) row_13003.1 gap_13003 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13007.1 gap_13007 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13009.1 gap_13009 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13033.1 gap_13033 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13037.1 gap_13037 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13043.1 gap_13043 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13049.1 gap_13049 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13063.1 gap_13063 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13093.1 gap_13093 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13099.1 gap_13099 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13103.1 gap_13103 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13109.1 gap_13109 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13121.1 gap_13121 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13127.1 gap_13127 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13147.1 gap_13147 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13151.1 gap_13151 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13159.1 gap_13159 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13163.1 gap_13163 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13171.1 gap_13171 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13177.1 gap_13177 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13183.1 gap_13183 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13187.1 gap_13187 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13217.1 gap_13217 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13219.1 gap_13219 (by norm_num)
  exact primeSpan_nil 13219

#print axioms reach_13219

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
