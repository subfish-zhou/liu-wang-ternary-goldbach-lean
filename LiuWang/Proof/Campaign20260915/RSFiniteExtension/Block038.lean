import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0382
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block038 : List ℕ := [8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199]

theorem complete_Block038 :
    ∀ p ∈ Finset.Ioc 8971 9199, p.Prime ↔ p ∈ primes_Block038 := by
  apply checked_of_primeSpan
  unfold primes_Block038
  apply primeSpan_cons (by norm_num) row_8999.1 gap_8999 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9001.1 gap_9001 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9007.1 gap_9007 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9011.1 gap_9011 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9013.1 gap_9013 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9029.1 gap_9029 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9041.1 gap_9041 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9043.1 gap_9043 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9049.1 gap_9049 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9059.1 gap_9059 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9067.1 gap_9067 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9091.1 gap_9091 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9103.1 gap_9103 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9109.1 gap_9109 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9127.1 gap_9127 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9133.1 gap_9133 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9137.1 gap_9137 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9151.1 gap_9151 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9157.1 gap_9157 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9161.1 gap_9161 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9173.1 gap_9173 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9181.1 gap_9181 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9187.1 gap_9187 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9199.1 gap_9199 (by norm_num)
  exact primeSpan_nil 9199

#print axioms reach_9199

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
