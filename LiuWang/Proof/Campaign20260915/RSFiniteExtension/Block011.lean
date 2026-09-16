import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0112
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block011 : List ℕ := [3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527]

theorem complete_Block011 :
    ∀ p ∈ Finset.Ioc 3323 3527, p.Prime ↔ p ∈ primes_Block011 := by
  apply checked_of_primeSpan
  unfold primes_Block011
  apply primeSpan_cons (by norm_num) row_3329.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3331.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3343.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3347.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3359.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3361.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3371.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3373.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3389.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3391.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3407.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3413.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3433.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3449.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3457.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3461.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3463.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3467.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3469.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3491.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3499.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3511.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3517.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3527.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 3527

#print axioms reach_3527

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
