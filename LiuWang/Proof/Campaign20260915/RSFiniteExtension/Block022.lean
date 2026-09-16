import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0222
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block022 : List ℕ := [5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743]

theorem complete_Block022 :
    ∀ p ∈ Finset.Ioc 5531 5743, p.Prime ↔ p ∈ primes_Block022 := by
  apply checked_of_primeSpan
  unfold primes_Block022
  apply primeSpan_cons (by norm_num) row_5557.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5563.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5569.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5573.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5581.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5591.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5623.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5639.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5641.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5647.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5651.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5653.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5657.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5659.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5669.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5683.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5689.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5693.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5701.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5711.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5717.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5737.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5741.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5743.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 5743

#print axioms reach_5743

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
