import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0122
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block012 : List ℕ := [3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697]

theorem complete_Block012 :
    ∀ p ∈ Finset.Ioc 3527 3697, p.Prime ↔ p ∈ primes_Block012 := by
  apply checked_of_primeSpan
  unfold primes_Block012
  apply primeSpan_cons (by norm_num) row_3529.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3533.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3539.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3541.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3547.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3557.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3559.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3571.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3581.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3583.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3593.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3607.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3613.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3617.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3623.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3631.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3637.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3643.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3659.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3671.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3673.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3677.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3691.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3697.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 3697

#print axioms reach_3697

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
