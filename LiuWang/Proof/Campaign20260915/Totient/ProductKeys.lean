import LiuWang.Proof.Campaign20260915.Totient.ProductData

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace LiuWang.Proof.Campaign20260915.Totient

theorem product_keys_286 {p : ℕ} (hl : 286 ≤ p) (hu : p < 318) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel

#print axioms product_keys_286

end LiuWang.Proof.Campaign20260915.Totient
