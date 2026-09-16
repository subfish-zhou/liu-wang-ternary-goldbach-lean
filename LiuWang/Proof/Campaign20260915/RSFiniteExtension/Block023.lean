import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0232
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block023 : List ℕ := [5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939]

theorem complete_Block023 :
    ∀ p ∈ Finset.Ioc 5743 5939, p.Prime ↔ p ∈ primes_Block023 := by
  apply checked_of_primeSpan
  unfold primes_Block023
  apply primeSpan_cons (by norm_num) row_5749.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5779.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5783.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5791.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5801.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5807.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5813.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5821.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5827.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5839.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5843.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5849.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5851.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5857.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5861.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5867.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5869.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5879.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5881.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5897.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5903.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5923.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5927.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5939.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 5939

#print axioms reach_5939

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
