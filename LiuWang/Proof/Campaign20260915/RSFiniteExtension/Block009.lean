import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0092
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block009 : List ℕ := [2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119]

theorem complete_Block009 :
    ∀ p ∈ Finset.Ioc 2903 3119, p.Prime ↔ p ∈ primes_Block009 := by
  apply checked_of_primeSpan
  unfold primes_Block009
  apply primeSpan_cons (by norm_num) row_2909.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2917.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2927.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2939.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2953.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2957.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2963.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2969.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2971.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_2999.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3001.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3011.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3019.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3023.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3037.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3041.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3049.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3061.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3067.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3079.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3083.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3089.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3109.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3119.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 3119

#print axioms reach_3119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
