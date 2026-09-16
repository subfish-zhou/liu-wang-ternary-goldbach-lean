import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0262
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block026 : List ℕ := [6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581]

theorem complete_Block026 :
    ∀ p ∈ Finset.Ioc 6359 6581, p.Prime ↔ p ∈ primes_Block026 := by
  apply checked_of_primeSpan
  unfold primes_Block026
  apply primeSpan_cons (by norm_num) row_6361.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6367.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6373.1 (primeGap_of_factors (ds := [2, 3, 2, 23, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6379.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6389.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6397.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6421.1 (primeGap_of_factors (ds := [2, 3, 2, 37, 2, 19, 2, 3, 2, 43, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6427.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6449.1 (primeGap_of_factors (ds := [2, 3, 2, 59, 2, 7, 2, 3, 2, 41, 2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6451.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6469.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 29, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6473.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6481.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6491.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2, 13, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6521.1 (primeGap_of_factors (ds := [2, 43, 2, 3, 2, 73, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6529.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 61, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6547.1 (primeGap_of_factors (ds := [2, 3, 2, 47, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6551.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6553.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6563.1 (primeGap_of_factors (ds := [2, 3, 2, 79, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6569.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6571.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6577.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6581.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) (by norm_num)
  exact primeSpan_nil 6581

#print axioms reach_6581

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
