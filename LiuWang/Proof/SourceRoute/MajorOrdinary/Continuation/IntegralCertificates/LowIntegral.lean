import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.WeightedMoments

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

theorem log_twelve_bounds :
    (2.4849066491 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ 2.4849066504 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  constructor <;> norm_num <;>
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9]

theorem tangent_twelve_intercept : logNu 12 - logNuD1 12 * 12 ≤ 4.06 := by
  have hl := log_twelve_bounds
  have hv : 0 < Real.log (12 : ℝ) := Real.log_pos (by norm_num)
  have h1 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2.4849066491) hl.1
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2.4849066491 ^ 2)
    (pow_le_pow_left₀ (by norm_num) hl.1 2)
  have he : logNu 12 - logNuD1 12 * 12 =
      1.781076 * (Real.log 12 - 1) + 2.50637 / Real.log 12 +
        2.50637 / Real.log 12 ^ 2 := by
    unfold logNu logNuD1
    ring
  rw [he]
  simp only [div_eq_mul_inv, one_mul] at h1 h2 ⊢
  norm_num at h1 h2
  linarith [hl.2]

theorem tangent_twelve_slope : logNuD1 12 ≤ 0.115 := by
  have h := one_div_le_one_div_of_le (pow_pos (Real.log_pos (by norm_num : (1 : ℝ) < 12)) 2)
    (pow_le_pow_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 12)).le log_twelve_bounds.2 2)
  unfold logNuD1
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  norm_num at h ⊢
  linarith

theorem nu_le_low_affine {x : ℝ} (hx : 100000 ≤ x) :
    nu x ≤ 4.06 + 0.115 * Real.log x := by
  have hu := log_input_ge hx
  have h := (nu_le_logNu hx).trans (logNu_le_tangent (by norm_num : (11.5 : ℝ) ≤ 12) hu)
  unfold tangent at h
  have hm := mul_le_mul_of_nonneg_right tangent_twelve_slope (by linarith : 0 ≤ Real.log x)
  linarith [tangent_twelve_intercept]

def lowPolynomial (u : ℝ) : ℝ :=
  (6 / 5) * ((4.06 + 0.115 * u) ^ 2 +
    (12 / 5) * 0.115 * (4.06 + 0.115 * u) + (72 / 25) * 0.115 ^ 2)

theorem low_primitive_eq (x : ℝ) :
    weightedSquarePrimitive (-5 / 6) 0 4.06 0.115 0 0 x =
      -x ^ (-5 / 6 : ℝ) * lowPolynomial (Real.log x) := by
  unfold weightedSquarePrimitive squarePrimitive
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, momentPrimitive, sub_zero]
  unfold lowPolynomial
  ring

theorem lowPolynomial_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ lowPolynomial u := by
  unfold lowPolynomial
  positivity

theorem lowPolynomial_monotone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    lowPolynomial u ≤ lowPolynomial v := by
  unfold lowPolynomial
  gcongr

theorem log_hundred_thousand_le : Real.log (100000 : ℝ) ≤ 11.513 := by
  rw [show (100000 : ℝ) = (2 * 5) ^ 5 by norm_num, Real.log_pow,
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem low_endpoint_power : (100000 : ℝ) ^ (-5 / 6 : ℝ) ≤ 0.00006813 := by
  have he : ((100000 : ℝ) ^ (-5 / 6 : ℝ)) ^ 6 = 1 / (100000 : ℝ) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num only
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    (by decide : 6 ≠ 0)).mp
  rw [he]
  norm_num

theorem original_low_fixed_integral :
    (∫ x in (100000 : ℝ)..10000000000, x ^ (-11 / 6 : ℝ) * nu x ^ 2) ≤ 0.0025 := by
  have hmajor : (∫ x in (100000 : ℝ)..10000000000, x ^ (-11 / 6 : ℝ) * nu x ^ 2) ≤
      ∫ x in (100000 : ℝ)..10000000000, x ^ (-5 / 6 - 1 : ℝ) *
        (4.06 + 0.115 * (Real.log x - 0) + 0 * (Real.log x - 0) ^ 2 +
          0 * (Real.log x - 0) ^ 3) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by
        have hi := nuKernel_intervalIntegrable (1 / 6) (a := 100000) (b := 10000000000)
          le_rfl (by norm_num)
        change IntervalIntegrable (fun x => x ^ (1 / 6 - 2 : ℝ) * nu x ^ 2) _ _ _ at hi
        simpa only [show (1 / 6 - 2 : ℝ) = -11 / 6 by norm_num] using hi)
      (weighted_square_integrable _ _ _ _ _ _ (by norm_num) (by norm_num))
    intro x hx
    simp only [sub_zero, zero_mul, add_zero, show (-5 / 6 - 1 : ℝ) = -11 / 6 by norm_num]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nu_pos hx.1).le (nu_le_low_affine hx.1) 2)
      (Real.rpow_nonneg (by linarith [hx.1]) _)
  rw [weighted_square_integral (by norm_num) (by norm_num) (by norm_num),
    low_primitive_eq, low_primitive_eq] at hmajor
  have hneg : -(10000000000 : ℝ) ^ (-5 / 6 : ℝ) *
      lowPolynomial (Real.log 10000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg (by norm_num) _))
      (lowPolynomial_nonneg (Real.log_nonneg (by norm_num)))
  have hp := mul_le_mul low_endpoint_power
    (lowPolynomial_monotone (Real.log_nonneg (by norm_num)) log_hundred_thousand_le)
    (lowPolynomial_nonneg (Real.log_nonneg (by norm_num))) (by norm_num)
  have hp' : (100000 : ℝ) ^ (-5 / 6 : ℝ) * lowPolynomial (Real.log 100000) ≤ 0.0025 :=
    hp.trans (by norm_num [lowPolynomial])
  linarith only [hmajor, hneg, hp']

theorem low_nuKernel_integral :
    (∫ x in (100000 : ℝ)..10000000000, nuKernel (1 / 6) x) ≤ 0.0025 := by
  simpa only [nuKernel, show (1 / 6 - 2 : ℝ) = -11 / 6 by norm_num] using
    original_low_fixed_integral

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
