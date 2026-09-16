import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0632
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block063 : List ℕ := [14657, 14669, 14683, 14699, 14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753, 14759, 14767, 14771, 14779, 14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851]

theorem complete_Block063 :
    ∀ p ∈ Finset.Ioc 14653 14851, p.Prime ↔ p ∈ primes_Block063 := by
  apply checked_of_primeSpan
  unfold primes_Block063
  apply primeSpan_cons (by norm_num) row_14657.1 gap_14657 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14669.1 gap_14669 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14683.1 gap_14683 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14699.1 gap_14699 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14713.1 gap_14713 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14717.1 gap_14717 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14723.1 gap_14723 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14731.1 gap_14731 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14737.1 gap_14737 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14741.1 gap_14741 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14747.1 gap_14747 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14753.1 gap_14753 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14759.1 gap_14759 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14767.1 gap_14767 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14771.1 gap_14771 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14779.1 gap_14779 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14783.1 gap_14783 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14797.1 gap_14797 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14813.1 gap_14813 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14821.1 gap_14821 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14827.1 gap_14827 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14831.1 gap_14831 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14843.1 gap_14843 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14851.1 gap_14851 (by norm_num)
  exact primeSpan_nil 14851

#print axioms reach_14851

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
