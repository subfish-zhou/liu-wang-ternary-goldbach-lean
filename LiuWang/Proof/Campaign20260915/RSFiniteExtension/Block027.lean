import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0272
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block027 : List ℕ := [6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803]

theorem complete_Block027 :
    ∀ p ∈ Finset.Ioc 6581 6803, p.Prime ↔ p ∈ primes_Block027 := by
  apply checked_of_primeSpan
  unfold primes_Block027
  apply primeSpan_cons (by norm_num) row_6599.1 gap_6599 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6607.1 gap_6607 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6619.1 gap_6619 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6637.1 gap_6637 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6653.1 gap_6653 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6659.1 gap_6659 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6661.1 gap_6661 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6673.1 gap_6673 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6679.1 gap_6679 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6689.1 gap_6689 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6691.1 gap_6691 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6701.1 gap_6701 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6703.1 gap_6703 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6709.1 gap_6709 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6719.1 gap_6719 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6733.1 gap_6733 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6737.1 gap_6737 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6761.1 gap_6761 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6763.1 gap_6763 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6779.1 gap_6779 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6781.1 gap_6781 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6791.1 gap_6791 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6793.1 gap_6793 (by norm_num)
  apply primeSpan_cons (by norm_num) row_6803.1 gap_6803 (by norm_num)
  exact primeSpan_nil 6803

#print axioms reach_6803

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
