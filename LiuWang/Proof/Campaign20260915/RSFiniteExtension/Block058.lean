import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0582
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block058 : List ℕ := [13469, 13477, 13487, 13499, 13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669, 13679, 13681, 13687, 13691, 13693, 13697]

theorem complete_Block058 :
    ∀ p ∈ Finset.Ioc 13463 13697, p.Prime ↔ p ∈ primes_Block058 := by
  apply checked_of_primeSpan
  unfold primes_Block058
  apply primeSpan_cons (by norm_num) row_13469.1 gap_13469 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13477.1 gap_13477 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13487.1 gap_13487 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13499.1 gap_13499 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13513.1 gap_13513 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13523.1 gap_13523 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13537.1 gap_13537 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13553.1 gap_13553 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13567.1 gap_13567 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13577.1 gap_13577 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13591.1 gap_13591 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13597.1 gap_13597 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13613.1 gap_13613 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13619.1 gap_13619 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13627.1 gap_13627 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13633.1 gap_13633 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13649.1 gap_13649 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13669.1 gap_13669 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13679.1 gap_13679 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13681.1 gap_13681 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13687.1 gap_13687 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13691.1 gap_13691 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13693.1 gap_13693 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13697.1 gap_13697 (by norm_num)
  exact primeSpan_nil 13697

#print axioms reach_13697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
