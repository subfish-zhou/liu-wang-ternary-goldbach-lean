import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0212
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block021 : List ℕ := [5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531]

theorem complete_Block021 :
    ∀ p ∈ Finset.Ioc 5351 5531, p.Prime ↔ p ∈ primes_Block021 := by
  apply checked_of_primeSpan
  unfold primes_Block021
  apply primeSpan_cons (by norm_num) row_5381.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5387.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5393.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5399.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5407.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5413.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5417.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5419.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5431.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5437.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5441.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5443.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5449.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5471.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5477.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5479.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5483.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5501.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5503.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5507.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5519.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5521.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5527.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_5531.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 5531

#print axioms reach_5531

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
