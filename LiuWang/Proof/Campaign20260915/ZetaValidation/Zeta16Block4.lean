import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16BlockData

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zeta16Block4_lower :
    (432 / 1000 : ℚ) ≤ (zeta16Block 4).1 ∧ (-609 / 1000 : ℚ) ≤ (zeta16Block 4).2 := by
  certify_zeta16_block

end LiuWang.Proof.Campaign20260915.ZetaValidation
