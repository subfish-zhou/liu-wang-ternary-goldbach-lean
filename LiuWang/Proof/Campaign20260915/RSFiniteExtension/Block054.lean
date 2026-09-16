import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0542
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block054 : List ℕ := [12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781]

theorem complete_Block054 :
    ∀ p ∈ Finset.Ioc 12553 12781, p.Prime ↔ p ∈ primes_Block054 := by
  apply checked_of_primeSpan
  unfold primes_Block054
  apply primeSpan_cons (by norm_num) row_12569.1 gap_12569 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12577.1 gap_12577 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12583.1 gap_12583 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12589.1 gap_12589 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12601.1 gap_12601 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12611.1 gap_12611 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12613.1 gap_12613 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12619.1 gap_12619 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12637.1 gap_12637 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12641.1 gap_12641 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12647.1 gap_12647 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12653.1 gap_12653 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12659.1 gap_12659 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12671.1 gap_12671 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12689.1 gap_12689 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12697.1 gap_12697 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12703.1 gap_12703 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12713.1 gap_12713 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12721.1 gap_12721 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12739.1 gap_12739 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12743.1 gap_12743 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12757.1 gap_12757 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12763.1 gap_12763 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12781.1 gap_12781 (by norm_num)
  exact primeSpan_nil 12781

#print axioms reach_12781

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
