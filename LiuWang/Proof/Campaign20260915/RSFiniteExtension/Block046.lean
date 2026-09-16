import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0462
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block046 : List ℕ := [10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973]

theorem complete_Block046 :
    ∀ p ∈ Finset.Ioc 10729 10973, p.Prime ↔ p ∈ primes_Block046 := by
  apply checked_of_primeSpan
  unfold primes_Block046
  apply primeSpan_cons (by norm_num) row_10733.1 gap_10733 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10739.1 gap_10739 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10753.1 gap_10753 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10771.1 gap_10771 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10781.1 gap_10781 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10789.1 gap_10789 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10799.1 gap_10799 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10831.1 gap_10831 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10837.1 gap_10837 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10847.1 gap_10847 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10853.1 gap_10853 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10859.1 gap_10859 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10861.1 gap_10861 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10867.1 gap_10867 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10883.1 gap_10883 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10889.1 gap_10889 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10891.1 gap_10891 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10903.1 gap_10903 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10909.1 gap_10909 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10937.1 gap_10937 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10939.1 gap_10939 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10949.1 gap_10949 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10957.1 gap_10957 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10973.1 gap_10973 (by norm_num)
  exact primeSpan_nil 10973

#print axioms reach_10973

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
