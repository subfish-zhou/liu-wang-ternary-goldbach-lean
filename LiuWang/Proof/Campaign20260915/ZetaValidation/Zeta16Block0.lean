import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16BlockData

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zeta16Block0_lower :
    (997 / 1000 : ℚ) ≤ (zeta16Block 0).1 ∧ (1012 / 1000 : ℚ) ≤ (zeta16Block 0).2 := by
  certify_zeta16_block

end LiuWang.Proof.Campaign20260915.ZetaValidation
