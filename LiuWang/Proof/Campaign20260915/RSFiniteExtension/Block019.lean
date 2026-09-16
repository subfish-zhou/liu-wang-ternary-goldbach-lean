import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0192
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block019 : List ℕ := [4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113]

theorem complete_Block019 :
    ∀ p ∈ Finset.Ioc 4937 5113, p.Prime ↔ p ∈ primes_Block019 := by
  apply checked_of_primeSpan
  unfold primes_Block019
  apply primeSpan_cons (by norm_num) row_4943.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4951.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4957.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4967.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4969.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4973.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4987.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4993.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4999.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5003.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5009.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5011.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5021.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5023.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5039.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5051.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5059.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5077.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5081.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5087.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5099.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5101.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5107.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5113.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 5113

#print axioms reach_5113

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
