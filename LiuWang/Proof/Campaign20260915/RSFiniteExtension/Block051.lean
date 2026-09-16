import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0512
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block051 : List ℕ := [11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119]

theorem complete_Block051 :
    ∀ p ∈ Finset.Ioc 11923 12119, p.Prime ↔ p ∈ primes_Block051 := by
  apply checked_of_primeSpan
  unfold primes_Block051
  apply primeSpan_cons (by norm_num) row_11927.1 gap_11927 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11933.1 gap_11933 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11939.1 gap_11939 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11941.1 gap_11941 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11953.1 gap_11953 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11959.1 gap_11959 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11969.1 gap_11969 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11971.1 gap_11971 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11981.1 gap_11981 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11987.1 gap_11987 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12007.1 gap_12007 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12011.1 gap_12011 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12037.1 gap_12037 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12041.1 gap_12041 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12043.1 gap_12043 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12049.1 gap_12049 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12071.1 gap_12071 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12073.1 gap_12073 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12097.1 gap_12097 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12101.1 gap_12101 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12107.1 gap_12107 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12109.1 gap_12109 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12113.1 gap_12113 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12119.1 gap_12119 (by norm_num)
  exact primeSpan_nil 12119

#print axioms reach_12119

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
