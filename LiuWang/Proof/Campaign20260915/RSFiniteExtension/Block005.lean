import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0052
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block005 : List ℕ := [2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347]

theorem complete_Block005 :
    ∀ p ∈ Finset.Ioc 2143 2347, p.Prime ↔ p ∈ primes_Block005 := by
  apply checked_of_primeSpan
  unfold primes_Block005
  apply primeSpan_cons (by norm_num) row_2153.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2161.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2179.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2203.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2207.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2213.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2221.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2237.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2239.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2243.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2251.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2267.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2269.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2273.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2281.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2287.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2293.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2297.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2309.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2311.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2333.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2339.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2341.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2347.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 2347

#print axioms reach_2347

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
