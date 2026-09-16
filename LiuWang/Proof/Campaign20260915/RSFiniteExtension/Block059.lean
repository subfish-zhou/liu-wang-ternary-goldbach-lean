import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0592
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block059 : List ℕ := [13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799, 13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907]

theorem complete_Block059 :
    ∀ p ∈ Finset.Ioc 13697 13907, p.Prime ↔ p ∈ primes_Block059 := by
  apply checked_of_primeSpan
  unfold primes_Block059
  apply primeSpan_cons (by norm_num) row_13709.1 gap_13709 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13711.1 gap_13711 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13721.1 gap_13721 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13723.1 gap_13723 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13729.1 gap_13729 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13751.1 gap_13751 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13757.1 gap_13757 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13759.1 gap_13759 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13763.1 gap_13763 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13781.1 gap_13781 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13789.1 gap_13789 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13799.1 gap_13799 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13807.1 gap_13807 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13829.1 gap_13829 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13831.1 gap_13831 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13841.1 gap_13841 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13859.1 gap_13859 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13873.1 gap_13873 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13877.1 gap_13877 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13879.1 gap_13879 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13883.1 gap_13883 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13901.1 gap_13901 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13903.1 gap_13903 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13907.1 gap_13907 (by norm_num)
  exact primeSpan_nil 13907

#print axioms reach_13907

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
