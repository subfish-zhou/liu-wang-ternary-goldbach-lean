import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0452
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block045 : List ℕ := [10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729]

theorem complete_Block045 :
    ∀ p ∈ Finset.Ioc 10499 10729, p.Prime ↔ p ∈ primes_Block045 := by
  apply checked_of_primeSpan
  unfold primes_Block045
  apply primeSpan_cons (by norm_num) row_10501.1 gap_10501 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10513.1 gap_10513 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10529.1 gap_10529 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10531.1 gap_10531 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10559.1 gap_10559 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10567.1 gap_10567 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10589.1 gap_10589 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10597.1 gap_10597 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10601.1 gap_10601 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10607.1 gap_10607 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10613.1 gap_10613 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10627.1 gap_10627 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10631.1 gap_10631 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10639.1 gap_10639 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10651.1 gap_10651 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10657.1 gap_10657 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10663.1 gap_10663 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10667.1 gap_10667 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10687.1 gap_10687 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10691.1 gap_10691 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10709.1 gap_10709 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10711.1 gap_10711 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10723.1 gap_10723 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10729.1 gap_10729 (by norm_num)
  exact primeSpan_nil 10729

#print axioms reach_10729

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
