import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0082
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block008 : List ℕ := [2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903]

theorem complete_Block008 :
    ∀ p ∈ Finset.Ioc 2713 2903, p.Prime ↔ p ∈ primes_Block008 := by
  apply checked_of_primeSpan
  unfold primes_Block008
  apply primeSpan_cons (by norm_num) row_2719.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2729.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2731.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2741.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2749.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2753.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2767.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2777.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2789.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2791.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2797.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2801.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2803.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2819.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2833.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2837.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2843.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2851.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2857.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2861.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2879.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2887.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2897.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2903.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 2903

#print axioms reach_2903

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
