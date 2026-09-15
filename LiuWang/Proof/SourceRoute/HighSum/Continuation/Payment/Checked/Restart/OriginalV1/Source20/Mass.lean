import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.MassIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

theorem source19_real_parameter {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    sourceMass N q alpha ≤ sourceP N *
      (nonprincipalDecimal (sourceP N) (sourceT N) / sourceT N +
        ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
          nonprincipalDecimal (sourceP N) y) := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hP : 0 < sourceP N := by
    unfold sourceP
    positivity
  have hlog : 10 ≤ Real.log (sourceP N) := by
    rw [Parameters.log_sourceP]
    linarith [(source_log_bounds hL).1]
  have hu := Parameters.omegaCutoff_ge (NeZero.pos q) hq
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have hu0 : 0 < omegaCutoff N q := by linarith
  have hT0 := hu0.trans_le huT
  have hcount {y : ℝ} (hy : 3.36 ≤ y) :=
    family_real_parameter q hP hlog hq ha hy
  have hend := div_le_div_of_nonneg_right (hcount (hu.trans huT)) hT0.le
  have hint : (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * (familyCount q alpha y : ℝ)) ≤
      ∫ y in omegaCutoff N q..sourceT N,
        sourceP N * (heightKernel y * nonprincipalDecimal (sourceP N) y) := by
    apply intervalIntegral.integral_mono_on huT (family_height_integrable q alpha hu0 huT)
      ((decimal_integrable hP hu0 huT).const_mul (sourceP N))
    intro y hy
    have hh := mul_le_mul_of_nonneg_left (hcount (hu.trans hy.1))
      (show 0 ≤ heightKernel y by unfold heightKernel; positivity)
    convert! hh using 1
    ring
  rw [intervalIntegral.integral_const_mul] at hint
  have hs := (sourceMass_le_full_height hN hq alpha).trans (add_le_add hend hint)
  exact hs.trans_eq (by ring)

theorem sourceMass_le_original51 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    sourceMass N q alpha ≤ 51 * sourceP N * Real.log (sourceL N) ^ 2 := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hP : 0 < sourceP N := by
    unfold sourceP
    positivity
  have hlog : 10 ≤ Real.log (sourceP N) := by
    rw [Parameters.log_sourceP]
    linarith [(source_log_bounds hL).1]
  have hu := Parameters.omegaCutoff_ge (NeZero.pos q) hq
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have hu0 : 0 < omegaCutoff N q := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (decimal_integrable hP (by norm_num : (0 : ℝ) < 3.36) hu)
    (decimal_integrable hP hu0 huT)
  have hnon : 0 ≤ ∫ y in (3.36 : ℝ)..omegaCutoff N q,
      heightKernel y * nonprincipalDecimal (sourceP N) y := by
    apply intervalIntegral.integral_nonneg hu
    intro y hy
    exact mul_nonneg (by unfold heightKernel; positivity)
      (real_decimal_nonneg hP hlog hy.1)
  have hi : (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * nonprincipalDecimal (sourceP N) y) ≤
      ∫ y in (3.36 : ℝ)..sourceT N, heightKernel y * nonprincipalDecimal (sourceP N) y := by
    linarith
  have hs := real_parameter_integral_paid hL
  change nonprincipalDecimal (sourceP N) (sourceT N) / sourceT N +
    (∫ y in (3.36 : ℝ)..sourceT N, heightKernel y * nonprincipalDecimal (sourceP N) y) ≤
    51 * Real.log (sourceL N) ^ 2 at hs
  have hp := mul_le_mul_of_nonneg_left ((add_le_add le_rfl hi).trans hs) hP.le
  exact (source19_real_parameter hN hq ha).trans (hp.trans_eq (by ring))

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
