import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0522
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block052 : List ℕ := [12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323, 12329, 12343, 12347, 12373]

theorem complete_Block052 :
    ∀ p ∈ Finset.Ioc 12119 12373, p.Prime ↔ p ∈ primes_Block052 := by
  apply checked_of_primeSpan
  unfold primes_Block052
  apply primeSpan_cons (by norm_num) row_12143.1 gap_12143 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12149.1 gap_12149 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12157.1 gap_12157 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12161.1 gap_12161 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12163.1 gap_12163 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12197.1 gap_12197 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12203.1 gap_12203 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12211.1 gap_12211 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12227.1 gap_12227 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12239.1 gap_12239 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12241.1 gap_12241 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12251.1 gap_12251 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12253.1 gap_12253 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12263.1 gap_12263 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12269.1 gap_12269 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12277.1 gap_12277 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12281.1 gap_12281 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12289.1 gap_12289 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12301.1 gap_12301 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12323.1 gap_12323 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12329.1 gap_12329 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12343.1 gap_12343 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12347.1 gap_12347 (by norm_num)
  apply primeSpan_cons (by norm_num) row_12373.1 gap_12373 (by norm_num)
  exact primeSpan_nil 12373

#print axioms reach_12373

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
