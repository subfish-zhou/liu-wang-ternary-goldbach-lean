import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0242
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block024 : List ℕ := [5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173]

theorem complete_Block024 :
    ∀ p ∈ Finset.Ioc 5939 6173, p.Prime ↔ p ∈ primes_Block024 := by
  apply checked_of_primeSpan
  unfold primes_Block024
  apply primeSpan_cons (by norm_num) row_5953.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5981.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5987.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6007.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6011.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6029.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6037.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6043.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6047.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6053.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6067.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6073.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6079.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6089.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6091.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6101.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6113.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6121.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6131.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6133.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6143.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6151.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6163.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_6173.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 6173

#print axioms reach_6173

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
