import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0102
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block010 : List ℕ := [3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323]

theorem complete_Block010 :
    ∀ p ∈ Finset.Ioc 3119 3323, p.Prime ↔ p ∈ primes_Block010 := by
  apply checked_of_primeSpan
  unfold primes_Block010
  apply primeSpan_cons (by norm_num) row_3121.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3137.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3163.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3167.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3169.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3181.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3187.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3191.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3203.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3209.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3217.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3221.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3229.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3251.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3253.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3257.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3259.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3271.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3299.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3301.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3307.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3313.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3319.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3323.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 3323

#print axioms reach_3323

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
