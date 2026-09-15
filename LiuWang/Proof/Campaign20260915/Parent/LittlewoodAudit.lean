import LiuWang.Proof.Campaign20260915.ZetaWinding.LittlewoodIdentity
import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanXiSeries

/-! Parent consumption of the actual all-positive-height Littlewood identity.
The Lehman effective constants and finite-height zero certificate remain unpaid.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.Campaign20260915.Parent.LittlewoodAudit
open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem actual_littlewood {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.pi * (∫ t in u..v, turingS t) =
      horizontalLogMass v - horizontalLogMass u :=
  littlewood_identity hu huv

theorem actual_littlewood_mid {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.pi * (∫ t in u..v, turingSMid t) =
      horizontalLogMass v - horizontalLogMass u :=
  littlewood_identity_mid hu huv

#print axioms actual_littlewood
#print axioms actual_littlewood_mid
end LiuWang.Proof.Campaign20260915.Parent.LittlewoodAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.abs_log_norm_weierstrass_one
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.critical_polynomial_argument_positive
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass_hasDerivAt_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass_hasDerivAt_turingS
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontal_zero_log_integral_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_eq_sub_finite_exception
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_logDeriv_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_logDeriv_two_three
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_re_mul_horizontal
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.littlewood_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.littlewood_identity_mid
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.littlewood_on_regular_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.logDeriv_tail_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_norm_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_zeta_hasDerivAt_right
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_zeta_horizontal_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_zeta_horizontal_tendsto_zero
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.norm_logDeriv_zeta_decay
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.regular_height_neighborhood
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.regular_logDeriv_uniform_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.right_log_mass_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.turingS_eq_horizontal_logDeriv
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_eq_zero_log
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_far_bound
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_horizontal_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_integral_eq_kernel
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_integral_norm_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_integral_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_integral_tsum
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_shift_eq_zero_ratio
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiGenusLog_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiLogCorrection_critical_im
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiLogCorrection_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xiLogCorrection_horizontal_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_horizontal_log_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_horizontal_log_integral_eq
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_horizontal_ne_zero_ae
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_horizontal_unit_shift_integral
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_lehman_unit_shift_series
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_log_norm_eq_genus_sum
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.xi_zero_ratio_integral_summable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_finite_horizontal_log_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_horizontal_regular
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_logDeriv_horizontal_continuousAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_logDeriv_horizontal_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_log_norm_height_hasDerivAt
