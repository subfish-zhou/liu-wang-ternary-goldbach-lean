import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0312
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block031 : List ℕ := [7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669]

theorem complete_Block031 :
    ∀ p ∈ Finset.Ioc 7487 7669, p.Prime ↔ p ∈ primes_Block031 := by
  apply checked_of_primeSpan
  unfold primes_Block031
  apply primeSpan_cons (by norm_num) row_7489.1 gap_7489 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7499.1 gap_7499 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7507.1 gap_7507 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7517.1 gap_7517 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7523.1 gap_7523 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7529.1 gap_7529 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7537.1 gap_7537 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7541.1 gap_7541 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7547.1 gap_7547 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7549.1 gap_7549 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7559.1 gap_7559 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7561.1 gap_7561 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7573.1 gap_7573 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7577.1 gap_7577 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7583.1 gap_7583 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7589.1 gap_7589 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7591.1 gap_7591 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7603.1 gap_7603 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7607.1 gap_7607 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7621.1 gap_7621 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7639.1 gap_7639 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7643.1 gap_7643 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7649.1 gap_7649 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7669.1 gap_7669 (by norm_num)
  exact primeSpan_nil 7669

#print axioms reach_7669

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
