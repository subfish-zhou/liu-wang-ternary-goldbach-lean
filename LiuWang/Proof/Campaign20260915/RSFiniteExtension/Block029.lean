import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0292
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block029 : List ℕ := [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229]

theorem complete_Block029 :
    ∀ p ∈ Finset.Ioc 6997 7229, p.Prime ↔ p ∈ primes_Block029 := by
  apply checked_of_primeSpan
  unfold primes_Block029
  apply primeSpan_cons (by norm_num) row_7001.1 gap_7001 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7013.1 gap_7013 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7019.1 gap_7019 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7027.1 gap_7027 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7039.1 gap_7039 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7043.1 gap_7043 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7057.1 gap_7057 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7069.1 gap_7069 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7079.1 gap_7079 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7103.1 gap_7103 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7109.1 gap_7109 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7121.1 gap_7121 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7127.1 gap_7127 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7129.1 gap_7129 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7151.1 gap_7151 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7159.1 gap_7159 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7177.1 gap_7177 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7187.1 gap_7187 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7193.1 gap_7193 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7207.1 gap_7207 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7211.1 gap_7211 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7213.1 gap_7213 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7219.1 gap_7219 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7229.1 gap_7229 (by norm_num)
  exact primeSpan_nil 7229

#print axioms reach_7229

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
