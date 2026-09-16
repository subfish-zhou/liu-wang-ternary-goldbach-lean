import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0552
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block055 : List ℕ := [12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001]

theorem complete_Block055 :
    ∀ p ∈ Finset.Ioc 12781 13001, p.Prime ↔ p ∈ primes_Block055 := by
  apply checked_of_primeSpan
  unfold primes_Block055
  apply primeSpan_cons (by norm_num) row_12791.1 gap_12791 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12799.1 gap_12799 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12809.1 gap_12809 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12821.1 gap_12821 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12823.1 gap_12823 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12829.1 gap_12829 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12841.1 gap_12841 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12853.1 gap_12853 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12889.1 gap_12889 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12893.1 gap_12893 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12899.1 gap_12899 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12907.1 gap_12907 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12911.1 gap_12911 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12917.1 gap_12917 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12919.1 gap_12919 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12923.1 gap_12923 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12941.1 gap_12941 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12953.1 gap_12953 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12959.1 gap_12959 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12967.1 gap_12967 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12973.1 gap_12973 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12979.1 gap_12979 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12983.1 gap_12983 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13001.1 gap_13001 (by norm_num)
  exact primeSpan_nil 13001

#print axioms reach_13001

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
