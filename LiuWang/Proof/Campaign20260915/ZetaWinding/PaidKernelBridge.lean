import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.ZeroSeries
import LiuWang.Proof.Campaign20260915.ZetaWinding.LehmanReferenceBudget

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

theorem zeta_unit_shift_paid_kernel_lower {T : ℝ} (hT : T ≠ 0) :
    -(37 / 25 : ℝ) * (∑' p : RiemannXiDivisorZeroIndex,
      (1 / (horizontalAt T (3 / 2) - riemannXiDivisorZeroValue p)).re) -
      (∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanGammaLog T x) - Real.log Real.pi / 2 ≤
      ∫ x in (1 / 2 : ℝ)..(3 / 2), Real.log ‖riemannZeta (horizontalAt T x) /
        riemannZeta (horizontalAt T (x + 1))‖ := by
  have hk := ZetaLehmanKernel.horizontalLogMass_lehman_lower hT
  have hp := polynomial_shift_one_nonneg hT
  rw [lehman_shift_one_identity hT] at hk
  have ha : ∀ p : RiemannXiDivisorZeroIndex,
      horizontalAt T (3 / 2) ≠ riemannXiDivisorZeroValue p := by
    intro p he
    have hs := (BombieriVinogradov.SiegelWalfisz.riemannXiDivisorZeroValue_re_mem_Ioo p).2
    rw [← he] at hs
    norm_num [horizontalAt] at hs
  rw [xi_uncompensated_logDeriv ha] at hk
  change 0 ≤ ∫ x in (1 / 2 : ℝ)..(3 / 2), lehmanPoleLog T x at hp
  linarith

theorem integral_turingS_eq_left (a b : ℝ) :
    (∫ t in a..b, turingS t) = ∫ t in a..b, turingSLeft t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [turingS_eq_mid_ae_on_interval a b] with t ht htI
  have he := ht htI
  unfold turingSMid at he
  linarith

theorem turingSLeft_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable turingSLeft volume a b := by
  apply (turingS_intervalIntegrable a b).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [turingS_eq_mid_ae_on_interval a b] with t ht htI
  have he := ht htI
  unfold turingSMid at he
  linarith

theorem turingSMid_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable turingSMid volume a b := by
  exact ((turingS_intervalIntegrable a b).add (turingSLeft_intervalIntegrable a b)).div_const 2

theorem littlewood_identity_left {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.pi * (∫ t in a..b, turingSLeft t) =
      horizontalLogMass b - horizontalLogMass a := by
  rw [← integral_turingS_eq_left]
  exact littlewood_identity ha hab

#print axioms zeta_unit_shift_paid_kernel_lower
#print axioms integral_turingS_eq_left
#print axioms turingSLeft_intervalIntegrable
#print axioms turingSMid_intervalIntegrable
#print axioms littlewood_identity_left

end LiuWang.Proof.Campaign20260915.ZetaWinding
