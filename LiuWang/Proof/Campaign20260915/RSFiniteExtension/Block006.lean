import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0062
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block006 : List ℕ := [2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543]

theorem complete_Block006 :
    ∀ p ∈ Finset.Ioc 2347 2543, p.Prime ↔ p ∈ primes_Block006 := by
  apply checked_of_primeSpan
  unfold primes_Block006
  apply primeSpan_cons (by norm_num) row_2351.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2357.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2371.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2377.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2381.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2383.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2389.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2393.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2399.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2411.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2417.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2423.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2437.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2441.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2447.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2459.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2467.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2473.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2477.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2503.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2521.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2531.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2539.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2543.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 2543

#print axioms reach_2543

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
