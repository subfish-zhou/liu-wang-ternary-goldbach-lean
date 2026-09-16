import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0392
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block039 : List ℕ := [9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413]

theorem complete_Block039 :
    ∀ p ∈ Finset.Ioc 9199 9413, p.Prime ↔ p ∈ primes_Block039 := by
  apply checked_of_primeSpan
  unfold primes_Block039
  apply primeSpan_cons (by norm_num) row_9203.1 gap_9203 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9209.1 gap_9209 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9221.1 gap_9221 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9227.1 gap_9227 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9239.1 gap_9239 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9241.1 gap_9241 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9257.1 gap_9257 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9277.1 gap_9277 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9281.1 gap_9281 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9283.1 gap_9283 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9293.1 gap_9293 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9311.1 gap_9311 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9319.1 gap_9319 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9323.1 gap_9323 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9337.1 gap_9337 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9341.1 gap_9341 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9343.1 gap_9343 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9349.1 gap_9349 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9371.1 gap_9371 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9377.1 gap_9377 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9391.1 gap_9391 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9397.1 gap_9397 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9403.1 gap_9403 (by norm_num)
  apply primeSpan_cons (by norm_num) row_9413.1 gap_9413 (by norm_num)
  exact primeSpan_nil 9413

#print axioms reach_9413

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
