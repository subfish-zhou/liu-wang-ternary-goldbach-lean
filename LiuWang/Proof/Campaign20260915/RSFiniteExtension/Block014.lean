import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0142
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block014 : List ℕ := [3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093]

theorem complete_Block014 :
    ∀ p ∈ Finset.Ioc 3907 4093, p.Prime ↔ p ∈ primes_Block014 := by
  apply checked_of_primeSpan
  unfold primes_Block014
  apply primeSpan_cons (by norm_num) row_3911.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3917.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3919.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3923.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3929.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3931.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3943.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3947.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3967.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3989.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4001.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4003.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4007.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4013.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4019.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4021.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4027.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4049.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4051.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4057.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4073.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4079.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4091.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4093.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 4093

#print axioms reach_4093

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
