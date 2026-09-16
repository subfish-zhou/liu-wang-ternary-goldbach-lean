import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0652
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block065 : List ℕ := [15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233, 15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307]

theorem complete_Block065 :
    ∀ p ∈ Finset.Ioc 15101 15307, p.Prime ↔ p ∈ primes_Block065 := by
  apply checked_of_primeSpan
  unfold primes_Block065
  apply primeSpan_cons (by norm_num) row_15107.1 gap_15107 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15121.1 gap_15121 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15131.1 gap_15131 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15137.1 gap_15137 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15139.1 gap_15139 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15149.1 gap_15149 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15161.1 gap_15161 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15173.1 gap_15173 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15187.1 gap_15187 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15193.1 gap_15193 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15199.1 gap_15199 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15217.1 gap_15217 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15227.1 gap_15227 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15233.1 gap_15233 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15241.1 gap_15241 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15259.1 gap_15259 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15263.1 gap_15263 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15269.1 gap_15269 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15271.1 gap_15271 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15277.1 gap_15277 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15287.1 gap_15287 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15289.1 gap_15289 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15299.1 gap_15299 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15307.1 gap_15307 (by norm_num)
  exact primeSpan_nil 15307

#print axioms reach_15307

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
