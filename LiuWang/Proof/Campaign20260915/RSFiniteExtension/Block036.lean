import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0362
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block036 : List ℕ := [8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753]

theorem complete_Block036 :
    ∀ p ∈ Finset.Ioc 8573 8753, p.Prime ↔ p ∈ primes_Block036 := by
  apply checked_of_primeSpan
  unfold primes_Block036
  apply primeSpan_cons (by norm_num) row_8581.1 gap_8581 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8597.1 gap_8597 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8599.1 gap_8599 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8609.1 gap_8609 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8623.1 gap_8623 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8627.1 gap_8627 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8629.1 gap_8629 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8641.1 gap_8641 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8647.1 gap_8647 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8663.1 gap_8663 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8669.1 gap_8669 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8677.1 gap_8677 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8681.1 gap_8681 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8689.1 gap_8689 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8693.1 gap_8693 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8699.1 gap_8699 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8707.1 gap_8707 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8713.1 gap_8713 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8719.1 gap_8719 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8731.1 gap_8731 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8737.1 gap_8737 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8741.1 gap_8741 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8747.1 gap_8747 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8753.1 gap_8753 (by norm_num)
  exact primeSpan_nil 8753

#print axioms reach_8753

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
