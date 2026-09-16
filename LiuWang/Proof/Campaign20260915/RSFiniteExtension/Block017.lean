import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0172
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block017 : List ℕ := [4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721]

theorem complete_Block017 :
    ∀ p ∈ Finset.Ioc 4513 4721, p.Prime ↔ p ∈ primes_Block017 := by
  apply checked_of_primeSpan
  unfold primes_Block017
  apply primeSpan_cons (by norm_num) row_4517.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4519.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4523.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4547.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4549.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4561.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4567.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4583.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4591.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4597.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4603.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4621.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4637.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4639.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4643.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4649.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4651.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4657.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4663.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4673.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4679.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4691.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4703.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4721.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 4721

#print axioms reach_4721

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
