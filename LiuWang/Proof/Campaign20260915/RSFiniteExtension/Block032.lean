import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0322
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block032 : List ℕ := [7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879]

theorem complete_Block032 :
    ∀ p ∈ Finset.Ioc 7669 7879, p.Prime ↔ p ∈ primes_Block032 := by
  apply checked_of_primeSpan
  unfold primes_Block032
  apply primeSpan_cons (by norm_num) row_7673.1 gap_7673 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7681.1 gap_7681 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7687.1 gap_7687 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7691.1 gap_7691 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7699.1 gap_7699 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7703.1 gap_7703 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7717.1 gap_7717 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7723.1 gap_7723 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7727.1 gap_7727 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7741.1 gap_7741 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7753.1 gap_7753 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7757.1 gap_7757 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7759.1 gap_7759 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7789.1 gap_7789 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7793.1 gap_7793 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7817.1 gap_7817 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7823.1 gap_7823 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7829.1 gap_7829 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7841.1 gap_7841 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7853.1 gap_7853 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7867.1 gap_7867 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7873.1 gap_7873 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7877.1 gap_7877 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7879.1 gap_7879 (by norm_num)
  exact primeSpan_nil 7879

#print axioms reach_7879

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
