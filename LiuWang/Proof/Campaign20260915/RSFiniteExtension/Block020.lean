import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0202
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block020 : List ℕ := [5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351]

theorem complete_Block020 :
    ∀ p ∈ Finset.Ioc 5113 5351, p.Prime ↔ p ∈ primes_Block020 := by
  apply checked_of_primeSpan
  unfold primes_Block020
  apply primeSpan_cons (by norm_num) row_5119.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5147.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5153.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5167.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5171.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5179.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5189.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5197.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5209.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5227.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5231.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5233.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5237.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5261.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5273.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5279.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5281.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5297.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5303.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5309.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5323.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5333.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5347.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5351.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 5351

#print axioms reach_5351

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
