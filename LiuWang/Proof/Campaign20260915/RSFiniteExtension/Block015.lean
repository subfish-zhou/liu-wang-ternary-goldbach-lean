import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0152
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block015 : List ℕ := [4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283]

theorem complete_Block015 :
    ∀ p ∈ Finset.Ioc 4093 4283, p.Prime ↔ p ∈ primes_Block015 := by
  apply checked_of_primeSpan
  unfold primes_Block015
  apply primeSpan_cons (by norm_num) row_4099.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4111.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4127.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4129.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4133.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4139.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4153.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4157.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4159.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4177.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4201.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4211.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4217.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4219.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4229.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4231.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4241.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4243.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4253.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4259.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4261.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4271.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4273.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4283.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 4283

#print axioms reach_4283

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
