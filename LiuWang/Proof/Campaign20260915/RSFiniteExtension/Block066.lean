import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0662
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block066 : List ℕ := [15313, 15319, 15329, 15331, 15349, 15359, 15361, 15373, 15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473, 15493, 15497, 15511, 15527]

theorem complete_Block066 :
    ∀ p ∈ Finset.Ioc 15307 15527, p.Prime ↔ p ∈ primes_Block066 := by
  apply checked_of_primeSpan
  unfold primes_Block066
  apply primeSpan_cons (by norm_num) row_15313.1 gap_15313 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15319.1 gap_15319 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15329.1 gap_15329 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15331.1 gap_15331 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15349.1 gap_15349 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15359.1 gap_15359 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15361.1 gap_15361 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15373.1 gap_15373 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15377.1 gap_15377 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15383.1 gap_15383 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15391.1 gap_15391 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15401.1 gap_15401 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15413.1 gap_15413 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15427.1 gap_15427 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15439.1 gap_15439 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15443.1 gap_15443 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15451.1 gap_15451 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15461.1 gap_15461 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15467.1 gap_15467 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15473.1 gap_15473 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15493.1 gap_15493 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15497.1 gap_15497 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15511.1 gap_15511 (by norm_num)
  apply primeSpan_cons (by norm_num) row_15527.1 gap_15527 (by norm_num)
  exact primeSpan_nil 15527

#print axioms reach_15527

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
