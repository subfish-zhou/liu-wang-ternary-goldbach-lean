import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Leaf0162
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.GapCompleteness

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block016 : List ℕ := [4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513]

theorem complete_Block016 :
    ∀ p ∈ Finset.Ioc 4283 4513, p.Prime ↔ p ∈ primes_Block016 := by
  apply checked_of_primeSpan
  unfold primes_Block016
  apply primeSpan_cons (by norm_num) row_4289.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4297.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4327.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4337.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4339.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4349.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4357.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4363.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4373.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4391.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4397.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4409.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4421.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4423.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4441.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4447.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4451.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4457.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4463.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4481.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4483.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4493.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4507.1 (by decide +kernel) (by norm_num)
  apply primeSpan_cons (by norm_num) row_4513.1 (by decide +kernel) (by norm_num)
  exact primeSpan_nil 4513

#print axioms reach_4513

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
