import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0342
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block034 : List ℕ := [8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317]

theorem complete_Block034 :
    ∀ p ∈ Finset.Ioc 8111 8317, p.Prime ↔ p ∈ primes_Block034 := by
  apply checked_of_primeSpan
  unfold primes_Block034
  apply primeSpan_cons (by norm_num) row_8117.1 gap_8117 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8123.1 gap_8123 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8147.1 gap_8147 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8161.1 gap_8161 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8167.1 gap_8167 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8171.1 gap_8171 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8179.1 gap_8179 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8191.1 gap_8191 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8209.1 gap_8209 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8219.1 gap_8219 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8221.1 gap_8221 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8231.1 gap_8231 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8233.1 gap_8233 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8237.1 gap_8237 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8243.1 gap_8243 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8263.1 gap_8263 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8269.1 gap_8269 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8273.1 gap_8273 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8287.1 gap_8287 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8291.1 gap_8291 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8293.1 gap_8293 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8297.1 gap_8297 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8311.1 gap_8311 (by norm_num)
  apply primeSpan_cons (by norm_num) row_8317.1 gap_8317 (by norm_num)
  exact primeSpan_nil 8317

#print axioms reach_8317

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
