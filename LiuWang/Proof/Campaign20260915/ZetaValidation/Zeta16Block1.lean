import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16BlockData

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zeta16Block1_lower :
    (148 / 1000 : ℚ) ≤ (zeta16Block 1).1 ∧ (367 / 1000 : ℚ) ≤ (zeta16Block 1).2 := by
  certify_zeta16_block

end LiuWang.Proof.Campaign20260915.ZetaValidation
