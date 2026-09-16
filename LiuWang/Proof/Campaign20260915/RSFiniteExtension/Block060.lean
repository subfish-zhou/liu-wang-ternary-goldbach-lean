import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0602
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block060 : List ℕ := [13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999, 14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149, 14153, 14159, 14173]

theorem complete_Block060 :
    ∀ p ∈ Finset.Ioc 13907 14173, p.Prime ↔ p ∈ primes_Block060 := by
  apply checked_of_primeSpan
  unfold primes_Block060
  apply primeSpan_cons (by norm_num) row_13913.1 gap_13913 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13921.1 gap_13921 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13931.1 gap_13931 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13933.1 gap_13933 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13963.1 gap_13963 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13967.1 gap_13967 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13997.1 gap_13997 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13999.1 gap_13999 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14009.1 gap_14009 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14011.1 gap_14011 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14029.1 gap_14029 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14033.1 gap_14033 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14051.1 gap_14051 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14057.1 gap_14057 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14071.1 gap_14071 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14081.1 gap_14081 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14083.1 gap_14083 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14087.1 gap_14087 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14107.1 gap_14107 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14143.1 gap_14143 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14149.1 gap_14149 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14153.1 gap_14153 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14159.1 gap_14159 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14173.1 gap_14173 (by norm_num)
  exact primeSpan_nil 14173

#print axioms reach_14173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
