import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0072
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block007 : List ℕ := [2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713]

theorem complete_Block007 :
    ∀ p ∈ Finset.Ioc 2543 2713, p.Prime ↔ p ∈ primes_Block007 := by
  apply checked_of_primeSpan
  unfold primes_Block007
  apply primeSpan_cons (by norm_num) row_2549.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2551.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2557.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2579.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2591.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2593.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2609.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2617.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2621.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2633.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2647.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2657.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2659.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2663.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2671.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2677.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2683.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2687.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2689.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2693.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2699.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2707.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2711.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2713.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 2713

#print axioms reach_2713

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
