import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0502
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block050 : List ℕ := [11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923]

theorem complete_Block050 :
    ∀ p ∈ Finset.Ioc 11699 11923, p.Prime ↔ p ∈ primes_Block050 := by
  apply checked_of_primeSpan
  unfold primes_Block050
  apply primeSpan_cons (by norm_num) row_11701.1 gap_11701 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11717.1 gap_11717 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11719.1 gap_11719 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11731.1 gap_11731 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11743.1 gap_11743 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11777.1 gap_11777 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11779.1 gap_11779 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11783.1 gap_11783 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11789.1 gap_11789 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11801.1 gap_11801 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11807.1 gap_11807 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11813.1 gap_11813 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11821.1 gap_11821 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11827.1 gap_11827 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11831.1 gap_11831 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11833.1 gap_11833 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11839.1 gap_11839 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11863.1 gap_11863 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11867.1 gap_11867 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11887.1 gap_11887 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11897.1 gap_11897 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11903.1 gap_11903 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11909.1 gap_11909 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11923.1 gap_11923 (by norm_num)
  exact primeSpan_nil 11923

#print axioms reach_11923

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
