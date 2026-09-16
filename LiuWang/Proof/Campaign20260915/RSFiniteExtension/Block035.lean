import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0352
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block035 : List ℕ := [8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573]

theorem complete_Block035 :
    ∀ p ∈ Finset.Ioc 8317 8573, p.Prime ↔ p ∈ primes_Block035 := by
  apply checked_of_primeSpan
  unfold primes_Block035
  apply primeSpan_cons (by norm_num) row_8329.1 gap_8329 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8353.1 gap_8353 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8363.1 gap_8363 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8369.1 gap_8369 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8377.1 gap_8377 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8387.1 gap_8387 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8389.1 gap_8389 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8419.1 gap_8419 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8423.1 gap_8423 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8429.1 gap_8429 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8431.1 gap_8431 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8443.1 gap_8443 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8447.1 gap_8447 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8461.1 gap_8461 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8467.1 gap_8467 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8501.1 gap_8501 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8513.1 gap_8513 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8521.1 gap_8521 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8527.1 gap_8527 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8537.1 gap_8537 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8539.1 gap_8539 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8543.1 gap_8543 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8563.1 gap_8563 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8573.1 gap_8573 (by norm_num)
  exact primeSpan_nil 8573

#print axioms reach_8573

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
