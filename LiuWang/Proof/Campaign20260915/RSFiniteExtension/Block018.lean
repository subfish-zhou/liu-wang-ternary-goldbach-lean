import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0182
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block018 : List ℕ := [4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937]

theorem complete_Block018 :
    ∀ p ∈ Finset.Ioc 4721 4937, p.Prime ↔ p ∈ primes_Block018 := by
  apply checked_of_primeSpan
  unfold primes_Block018
  apply primeSpan_cons (by norm_num) row_4723.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4729.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4733.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4751.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4759.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4783.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4787.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4789.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4793.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4799.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4801.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4813.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4817.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4831.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4861.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4871.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4877.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4889.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4903.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4909.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4919.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4931.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4933.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4937.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 4937

#print axioms reach_4937

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
