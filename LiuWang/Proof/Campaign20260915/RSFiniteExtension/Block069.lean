import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0690
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block069 : List ℕ := [15973, 15991]

theorem complete_Block069 :
    ∀ p ∈ Finset.Ioc 15971 15991, p.Prime ↔ p ∈ primes_Block069 := by
  apply checked_of_primeSpan
  unfold primes_Block069
  apply primeSpan_cons (by norm_num) row_15973.1 gap_15973 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15991.1 gap_15991 (by norm_num)
  exact primeSpan_nil 15991

#print axioms reach_15991

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
