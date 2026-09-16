import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0472
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block047 : List ℕ := [10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197]

theorem complete_Block047 :
    ∀ p ∈ Finset.Ioc 10973 11197, p.Prime ↔ p ∈ primes_Block047 := by
  apply checked_of_primeSpan
  unfold primes_Block047
  apply primeSpan_cons (by norm_num) row_10979.1 gap_10979 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10987.1 gap_10987 (by norm_num)
  apply primeSpan_cons (by norm_num) row_10993.1 gap_10993 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11003.1 gap_11003 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11027.1 gap_11027 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11047.1 gap_11047 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11057.1 gap_11057 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11059.1 gap_11059 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11069.1 gap_11069 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11071.1 gap_11071 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11083.1 gap_11083 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11087.1 gap_11087 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11093.1 gap_11093 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11113.1 gap_11113 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11117.1 gap_11117 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11119.1 gap_11119 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11131.1 gap_11131 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11149.1 gap_11149 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11159.1 gap_11159 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11161.1 gap_11161 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11171.1 gap_11171 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11173.1 gap_11173 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11177.1 gap_11177 (by norm_num)
  apply primeSpan_cons (by norm_num) row_11197.1 gap_11197 (by norm_num)
  exact primeSpan_nil 11197

#print axioms reach_11197

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
