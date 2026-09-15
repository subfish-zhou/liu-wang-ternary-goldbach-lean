import LiuWang.Proof.Campaign20260915.ZetaValidation.HorizontalData

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem horizontal_coeff7 (j : ℕ) (hj : j < 8) :
    horizontalCoefficient (56 + j) + 1 / 1000 ≤ (power16Center (56 + j + 1)).1 := by
  interval_cases j <;> certify_horizontal_coefficient

theorem horizontal_tail_phase_rational :
    (power16Center 64).1 ≤ -1 / 100 ∧ 1 / 100 ≤ (power16Center 64).2 := by
  certify_horizontal_coefficient

end LiuWang.Proof.Campaign20260915.ZetaValidation
