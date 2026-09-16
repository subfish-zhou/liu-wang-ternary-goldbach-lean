import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0572
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block057 : List ℕ := [13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463]

theorem complete_Block057 :
    ∀ p ∈ Finset.Ioc 13219 13463, p.Prime ↔ p ∈ primes_Block057 := by
  apply checked_of_primeSpan
  unfold primes_Block057
  apply primeSpan_cons (by norm_num) row_13229.1 gap_13229 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13241.1 gap_13241 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13249.1 gap_13249 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13259.1 gap_13259 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13267.1 gap_13267 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13291.1 gap_13291 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13297.1 gap_13297 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13309.1 gap_13309 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13313.1 gap_13313 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13327.1 gap_13327 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13331.1 gap_13331 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13337.1 gap_13337 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13339.1 gap_13339 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13367.1 gap_13367 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13381.1 gap_13381 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13397.1 gap_13397 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13399.1 gap_13399 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13411.1 gap_13411 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13417.1 gap_13417 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13421.1 gap_13421 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13441.1 gap_13441 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13451.1 gap_13451 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13457.1 gap_13457 (by norm_num)
  apply primeSpan_cons (by norm_num) row_13463.1 gap_13463 (by norm_num)
  exact primeSpan_nil 13463

#print axioms reach_13463

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
