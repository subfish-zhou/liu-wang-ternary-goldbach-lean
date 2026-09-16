import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0302
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block030 : List ℕ := [7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487]

theorem complete_Block030 :
    ∀ p ∈ Finset.Ioc 7229 7487, p.Prime ↔ p ∈ primes_Block030 := by
  apply checked_of_primeSpan
  unfold primes_Block030
  apply primeSpan_cons (by norm_num) row_7237.1 gap_7237 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7243.1 gap_7243 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7247.1 gap_7247 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7253.1 gap_7253 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7283.1 gap_7283 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7297.1 gap_7297 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7307.1 gap_7307 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7309.1 gap_7309 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7321.1 gap_7321 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7331.1 gap_7331 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7333.1 gap_7333 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7349.1 gap_7349 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7351.1 gap_7351 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7369.1 gap_7369 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7393.1 gap_7393 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7411.1 gap_7411 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7417.1 gap_7417 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7433.1 gap_7433 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7451.1 gap_7451 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7457.1 gap_7457 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7459.1 gap_7459 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7477.1 gap_7477 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7481.1 gap_7481 (by norm_num)
  apply primeSpan_cons (by norm_num) row_7487.1 gap_7487 (by norm_num)
  exact primeSpan_nil 7487

#print axioms reach_7487

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
