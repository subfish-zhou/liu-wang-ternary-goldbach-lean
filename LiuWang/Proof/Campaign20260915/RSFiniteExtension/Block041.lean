import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0412
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block041 : List ℕ := [9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829]

theorem complete_Block041 :
    ∀ p ∈ Finset.Ioc 9623 9829, p.Prime ↔ p ∈ primes_Block041 := by
  apply checked_of_primeSpan
  unfold primes_Block041
  apply primeSpan_cons (by norm_num) row_9629.1 gap_9629 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9631.1 gap_9631 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9643.1 gap_9643 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9649.1 gap_9649 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9661.1 gap_9661 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9677.1 gap_9677 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9679.1 gap_9679 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9689.1 gap_9689 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9697.1 gap_9697 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9719.1 gap_9719 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9721.1 gap_9721 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9733.1 gap_9733 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9739.1 gap_9739 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9743.1 gap_9743 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9749.1 gap_9749 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9767.1 gap_9767 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9769.1 gap_9769 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9781.1 gap_9781 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9787.1 gap_9787 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9791.1 gap_9791 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9803.1 gap_9803 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9811.1 gap_9811 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9817.1 gap_9817 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9829.1 gap_9829 (by norm_num)
  exact primeSpan_nil 9829

#print axioms reach_9829

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
