import LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail.BoundaryReserve
import LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections.Main

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.Campaign20260915.RSPrimePowerCorrections

namespace LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail

theorem actual_prime_power_correction_reserve {x : ℝ} (hx : 0 < x)
    (hL : 5000 ≤ Real.log x) :
    1.84 + (Chebyshev.psi x - Chebyshev.theta x) + rsTrivialKernel x <
      x * epsilon x / 8 := by
  have hp := psi_sub_theta_lt_elementary hx
  have hb := elementary_correction_reserve hx hL
  linarith

theorem actual_theta_delta_reserve {x : ℝ} (hx : 0 < x)
    (hL : 5000 ≤ Real.log x) :
    x * rsEpsilon 1 (smoothingStep (Real.log x)) +
      1.84 + (Chebyshev.psi x - Chebyshev.theta x) + rsTrivialKernel x <
        x * epsilon x := by
  have he := mul_le_mul_of_nonneg_left (smoothing_epsilon_reserve hL) hx.le
  have hc := actual_prime_power_correction_reserve hx hL
  linarith

#print axioms actual_prime_power_correction_reserve
#print axioms actual_theta_delta_reserve

end LiuWang.Proof.Campaign20260915.RSEffectiveThetaTail
