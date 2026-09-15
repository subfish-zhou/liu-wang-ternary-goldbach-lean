import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16BlockData

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem zeta16Block7_lower :
    (-798 / 1000 : ℚ) ≤ (zeta16Block 7).1 ∧ (-294 / 1000 : ℚ) ≤ (zeta16Block 7).2 := by
  certify_zeta16_block

theorem zeta16TailCenter_lower :
    (334 / 1000 : ℚ) ≤ zeta16TailCenter.1 ∧ (378 / 1000 : ℚ) ≤ zeta16TailCenter.2 := by
  certify_zeta16_block

end LiuWang.Proof.Campaign20260915.ZetaValidation
