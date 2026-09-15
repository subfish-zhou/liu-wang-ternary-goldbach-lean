import LiuWang.Proof.Campaign20260915.ZetaWinding.CountingIntegral

/-! Parent consumption of actual Turing count-area and logarithmic-tail results.
The Littlewood identity and the effective Lehman bound remain unproved here.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.Parent.ZetaTuringIntegralAudit
open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem actual_count_area {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, turingS t) =
      (∑ z ∈ positiveValues b, (analyticOrderNatAt riemannZeta z : ℝ) *
        (b - max a z.im)) - (b - a) -
          (∫ t in a..b, criticalGammaArgument t) / Real.pi :=
  integral_turingS_eq_zero_areas hab

theorem actual_horizontal_log_tail (T : ℝ) {a : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun x => log (riemannZeta (horizontalAt T x))) (Set.Ioi a) ∧
    ‖∫ x in Set.Ioi a, log (riemannZeta (horizontalAt T x))‖ ≤
      3 * 2 ^ (2 - a) / Real.log 2 :=
  ⟨log_zeta_right_integrable T ha, norm_integral_log_zeta_right_le T ha⟩

#print axioms actual_count_area
#print axioms actual_horizontal_log_tail
end LiuWang.Proof.Campaign20260915.Parent.ZetaTuringIntegralAudit

#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.mem_positiveValues
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_order_conj
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zetaClosedCount_eq_two_positiveCount
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_mono
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_right_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_intervalIntegrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_sixteen
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_norm_horizontal
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.logNormPrimitive_hasDerivAt
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_norm_horizontal_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_log_norm_horizontal
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_norm_zero_factor_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_log_norm_zero_factor
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_log_norm_zero_ratio
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_horizontal_log_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_finite_zero_log_contribution
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_sub_one_decay
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.norm_log_zeta_decay
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_tail_envelope_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_log_tail_envelope
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.log_zeta_right_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.norm_integral_log_zeta_right_le
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.finite_left_clearance
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_left_plateau
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.criticalGammaArgument_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.turingS_tendsto_left
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.turingS_right_continuous
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.turingS_jump
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.turingS_intervalIntegrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.turingS_eq_mid_ae_on_interval
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_turingS_eq_mid
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_horizontal_log_integrable_Ioi
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass_split
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.horizontalLogMass_truncation_error
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_shift_one_log_ae
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zeta_shift_one_log_integrable
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.lehman_shift_one_identity
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.polynomial_shift_one_nonneg
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.ordinate_step_monotone
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_ordinate_step
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.positiveCount_eq_finite_steps
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_positiveCount_eq_zero_areas
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.integral_turingS_eq_zero_areas
#print axioms LiuWang.Proof.Campaign20260915.ZetaWinding.zero_area_lower_bound
