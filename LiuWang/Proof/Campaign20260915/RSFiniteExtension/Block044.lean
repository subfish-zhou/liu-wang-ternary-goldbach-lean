import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0442
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block044 : List ℕ := [10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459, 10463, 10477, 10487, 10499]

theorem complete_Block044 :
    ∀ p ∈ Finset.Ioc 10271 10499, p.Prime ↔ p ∈ primes_Block044 := by
  apply checked_of_primeSpan
  unfold primes_Block044
  apply primeSpan_cons (by norm_num) row_10273.1 gap_10273 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10289.1 gap_10289 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10301.1 gap_10301 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10303.1 gap_10303 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10313.1 gap_10313 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10321.1 gap_10321 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10331.1 gap_10331 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10333.1 gap_10333 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10337.1 gap_10337 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10343.1 gap_10343 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10357.1 gap_10357 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10369.1 gap_10369 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10391.1 gap_10391 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10399.1 gap_10399 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10427.1 gap_10427 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10429.1 gap_10429 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10433.1 gap_10433 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10453.1 gap_10453 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10457.1 gap_10457 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10459.1 gap_10459 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10463.1 gap_10463 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10477.1 gap_10477 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10487.1 gap_10487 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10499.1 gap_10499 (by norm_num)
  exact primeSpan_nil 10499

#print axioms reach_10499

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
