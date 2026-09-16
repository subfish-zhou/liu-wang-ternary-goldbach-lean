import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0612
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block061 : List ℕ := [14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431]

theorem complete_Block061 :
    ∀ p ∈ Finset.Ioc 14173 14431, p.Prime ↔ p ∈ primes_Block061 := by
  apply checked_of_primeSpan
  unfold primes_Block061
  apply primeSpan_cons (by norm_num) row_14177.1 gap_14177 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14197.1 gap_14197 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14207.1 gap_14207 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14221.1 gap_14221 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14243.1 gap_14243 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14249.1 gap_14249 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14251.1 gap_14251 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14281.1 gap_14281 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14293.1 gap_14293 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14303.1 gap_14303 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14321.1 gap_14321 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14323.1 gap_14323 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14327.1 gap_14327 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14341.1 gap_14341 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14347.1 gap_14347 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14369.1 gap_14369 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14387.1 gap_14387 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14389.1 gap_14389 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14401.1 gap_14401 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14407.1 gap_14407 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14411.1 gap_14411 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14419.1 gap_14419 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14423.1 gap_14423 (by norm_num)
  apply primeSpan_cons (by norm_num) row_14431.1 gap_14431 (by norm_num)
  exact primeSpan_nil 14431

#print axioms reach_14431

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
