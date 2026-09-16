import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0252
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block025 : List ℕ := [6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359]

theorem complete_Block025 :
    ∀ p ∈ Finset.Ioc 6173 6359, p.Prime ↔ p ∈ primes_Block025 := by
  apply checked_of_primeSpan
  unfold primes_Block025
  apply primeSpan_cons (by norm_num) row_6197.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6199.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6203.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6211.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6217.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6221.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6229.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6247.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6257.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6263.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6269.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6271.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6277.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6287.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6299.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6301.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6311.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6317.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6323.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6329.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6337.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6343.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6353.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6359.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 6359

#print axioms reach_6359

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
