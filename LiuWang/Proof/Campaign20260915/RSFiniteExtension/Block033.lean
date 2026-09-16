import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0332
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block033 : List ℕ := [7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111]

theorem complete_Block033 :
    ∀ p ∈ Finset.Ioc 7879 8111, p.Prime ↔ p ∈ primes_Block033 := by
  apply checked_of_primeSpan
  unfold primes_Block033
  apply primeSpan_cons (by norm_num) row_7883.1 gap_7883 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7901.1 gap_7901 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7907.1 gap_7907 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7919.1 gap_7919 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7927.1 gap_7927 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7933.1 gap_7933 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7937.1 gap_7937 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7949.1 gap_7949 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7951.1 gap_7951 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7963.1 gap_7963 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7993.1 gap_7993 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8009.1 gap_8009 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8011.1 gap_8011 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8017.1 gap_8017 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8039.1 gap_8039 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8053.1 gap_8053 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8059.1 gap_8059 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8069.1 gap_8069 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8081.1 gap_8081 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8087.1 gap_8087 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8089.1 gap_8089 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8093.1 gap_8093 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8101.1 gap_8101 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8111.1 gap_8111 (by norm_num)
  exact primeSpan_nil 8111

#print axioms reach_8111

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
