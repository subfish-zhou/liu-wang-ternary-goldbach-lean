import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.Family

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

def massPrimitive (Q y : ℝ) : ℝ :=
  Real.log (Q * y) ^ 2 / (2 * Real.pi) - 0.874 * Real.log y -
    6.8423 * (Real.log (Q * y) + 1) / y - 15 / y

theorem decimal_integrable {Q u T : ℝ} (hQ : 0 < Q) (hu : 0 < u) (huT : u ≤ T) :
    IntervalIntegrable (fun y => heightKernel y * nonprincipalDecimal Q y) volume u T := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huT]
  have hl : ContinuousOn (fun y => Real.log (Q * y)) (Set.Icc u T) :=
    (continuousOn_const.mul continuousOn_id).log
      (fun y hy => mul_ne_zero hQ.ne' (hu.trans_le hy.1).ne')
  apply ContinuousOn.mul
  · exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero _ (hu.trans_le hy.1).ne')
  · unfold nonprincipalDecimal
    fun_prop

theorem massPrimitive_deriv {Q y : ℝ} (hQ : 0 < Q) (hy : 0 < y) :
    HasDerivAt (massPrimitive Q) (heightKernel y * nonprincipalDecimal Q y) y := by
  have hl : HasDerivAt (fun t : ℝ => Real.log (Q * t)) (1 / y) y := by
    convert (((hasDerivAt_id y).const_mul Q).log (mul_pos hQ hy).ne') using 1
    · rfl
    · simp only [id_eq, mul_one]
      field_simp
  have hh := ((((hl.pow 2).div_const (2 * Real.pi)).sub
      ((Real.hasDerivAt_log hy.ne').const_mul 0.874)).sub
      (((hl.add_const 1).const_mul 6.8423).div (hasDerivAt_id y) hy.ne')).sub
      ((hasDerivAt_const y (15 : ℝ)).div (hasDerivAt_id y) hy.ne')
  apply hh.congr_deriv
  dsimp only [heightKernel, nonprincipalDecimal, id_eq]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem decimal_height_integral {Q u T : ℝ} (hQ : 0 < Q) (hu : 0 < u) (huT : u ≤ T) :
    (∫ y in u..T, heightKernel y * nonprincipalDecimal Q y) =
      massPrimitive Q T - massPrimitive Q u := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    rw [Set.uIcc_of_le huT] at hy
    exact massPrimitive_deriv hQ (hu.trans_le hy.1)
  · exact decimal_integrable hQ hu huT

theorem decimal_endpoint_identity {Q u T : ℝ}
    (hQ : 0 < Q) (hu : 0 < u) (huT : u ≤ T) :
    nonprincipalDecimal Q T / T +
        (∫ y in u..T, heightKernel y * nonprincipalDecimal Q y) =
      (Real.log (Q * T) ^ 2 - Real.log (Q * u) ^ 2) / (2 * Real.pi) +
        Real.log (Q * T) / Real.pi - 0.874 * (1 + Real.log T - Real.log u) +
        (6.8423 * (Real.log (Q * u) + 1) + 15) / u - 6.8423 / T := by
  rw [decimal_height_integral hQ hu huT]
  unfold nonprincipalDecimal massPrimitive
  have hT := hu.trans_le huT
  field_simp
  ring

theorem real_parameter_integral_paid {L : ℝ} (hL : 3100 ≤ L) :
    nonprincipalDecimal (L ^ 3) (L ^ 15) / L ^ 15 +
        (∫ y in (3.36 : ℝ)..L ^ 15, heightKernel y * nonprincipalDecimal (L ^ 3) y) ≤
      51 * Real.log L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hl := (source_log_bounds hL).1
  have hc := (source_log_bounds hL).2
  have hc0 : 0 ≤ Real.log 3.36 := Real.log_nonneg (by norm_num)
  have hT : 3.36 ≤ L ^ 15 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 15
    norm_num at hh
    linarith
  rw [decimal_endpoint_identity (by positivity) (by norm_num) hT]
  rw [Real.log_mul (pow_ne_zero _ hL0.ne') (pow_ne_zero _ hL0.ne'),
    Real.log_mul (pow_ne_zero _ hL0.ne') (by norm_num), Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hp0 := Real.pi_pos
  have hp : (25 / 8 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hsq : (3 * Real.log L + Real.log 3.36) ^ 2 ≥ 9 * Real.log L ^ 2 := by
    nlinarith
  have hmain : ((3 * Real.log L + 15 * Real.log L) ^ 2 -
      (3 * Real.log L + Real.log 3.36) ^ 2) / (2 * Real.pi) ≤
      (101 / 2 : ℝ) * Real.log L ^ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (Real.log L))
    nlinarith
  have hlinear : (3 * Real.log L + 15 * Real.log L) / Real.pi ≤
      (144 / 25 : ℝ) * Real.log L := by
    apply (div_le_iff₀ hp0).mpr
    have hh := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ Real.log L)
    nlinarith
  have htail : 0 ≤ (6.8423 : ℝ) / L ^ 15 := by positivity
  nlinarith [sq_nonneg (Real.log L - 5)]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
