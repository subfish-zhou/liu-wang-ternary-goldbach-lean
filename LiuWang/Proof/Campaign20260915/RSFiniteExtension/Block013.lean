import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0132
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block013 : List ℕ := [3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907]

theorem complete_Block013 :
    ∀ p ∈ Finset.Ioc 3697 3907, p.Prime ↔ p ∈ primes_Block013 := by
  apply checked_of_primeSpan
  unfold primes_Block013
  apply primeSpan_cons (by norm_num) row_3701.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3709.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3719.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3727.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3733.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3739.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3761.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3767.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3769.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3779.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3793.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3797.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3803.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3821.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3823.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3833.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3847.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3851.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3853.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3863.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3877.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3881.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3889.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_3907.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 3907

#print axioms reach_3907

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
