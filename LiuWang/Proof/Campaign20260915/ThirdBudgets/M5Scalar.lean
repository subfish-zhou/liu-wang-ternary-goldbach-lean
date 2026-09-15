import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5Envelope
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.Endpoint

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem m5_nu_scaling {L : ℝ} (hL : 3100 ≤ L) :
    sourceNu (L ^ 6) ≤ 7.56 * (L / 3100) := by
  have h := Source524.real_parameter_scaling hL
    (x := 6) (by norm_num) le_rfl
  have hs := Source524.logNu_scaling h.1 (r := L / 3100) (by linarith)
    h.2.2.1 h.2.2.2
  have hc : Source524.logNu (6 * Real.log 3100) ≤ 7.56 :=
    Source524.endpoint_nu.trans (by norm_num)
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ L / 3100 by positivity)
  unfold sourceNu
  rw [Real.log_pow]
  simp only [Nat.cast_ofNat]
  exact hs.trans hp

theorem m5_scalar_exponent {L : ℝ} (hL : 3100 ≤ L) :
    (119 / 60 : ℝ) * Real.log L - (5 / 12 : ℝ) * Real.log (10 * Real.pi) -
      6 - 49.69 * Real.sqrt (L / 3100) ≤ -41.16 := by
  let r := Real.sqrt (L / 3100)
  have hr : 1 ≤ r := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ L / 3100 by linarith)
    simpa only [Real.sqrt_one] using h
  have hr0 : 0 < r := by linarith
  have hr2 : r ^ 2 = L / 3100 := Real.sq_sqrt (by positivity)
  have hid : L = 3100 * r ^ 2 := by linarith
  have hlog : Real.log L = Real.log 3100 + 2 * Real.log r := by
    rw [hid, Real.log_mul (by norm_num : (3100 : ℝ) ≠ 0) (pow_pos hr0 2).ne',
      Real.log_pow]
    norm_num
  have hb : Real.log L ≤ 8.04 + 2 * (r - 1) := by
    rw [hlog]
    linarith [log_3100_bounds.2, Real.log_le_sub_one_of_pos hr0]
  change (119 / 60 : ℝ) * Real.log L - (5 / 12 : ℝ) * Real.log (10 * Real.pi) -
    6 - 49.69 * r ≤ -41.16
  linarith [M6Certificate.log_ten_pi_bounds.1]

theorem m5_scalar_rational_certificate :
    ((12 * 37924 * 60 ^ 6 * 7.56 / 3100 : ℝ) * Real.exp (-41.16)) ≤
      0.00007 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 41
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have hs := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.16)
  have h := mul_le_mul hp hs (by norm_num) (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  norm_num only [show (41 : ℝ) + 0.16 = 41.16 by norm_num] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num at h ⊢
  linarith only [h]

theorem m5_scalar_factor_identity {L : ℝ} (hL : 0 < L) :
    L ^ (39 / 10 : ℝ) * (7.56 * (L / 3100)) *
        Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
        Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7)) =
      (7.56 / 3100 : ℝ) *
        Real.exp ((119 / 60 : ℝ) * Real.log L -
          (5 / 12 : ℝ) * Real.log (10 * Real.pi) -
          6 - 49.69 * Real.sqrt (L / 3100)) := by
  rw [Real.rpow_def_of_pos hL,
    Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0) (pow_pos hL 7).ne',
    Real.log_pow]
  simp only [Nat.cast_ofNat]
  have he : (119 / 60 : ℝ) * Real.log L - (5 / 12 : ℝ) * Real.log (10 * Real.pi) -
      6 - 49.69 * Real.sqrt (L / 3100) =
    Real.log L * (39 / 10 : ℝ) + Real.log L +
      (-6 - 49.69 * Real.sqrt (L / 3100)) +
      (-(5 / 12 : ℝ) * (Real.log (10 * Real.pi) + 7 * Real.log L)) := by ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hL]
  ring

theorem original_m5_scalar_paid {L : ℝ} (hL : 3100 ≤ L) :
    5 * L ^ (39 / 10 : ℝ) * sourceNu (L ^ 6) *
        (∫ t in Real.log (10 * Real.pi * L ^ 7)..Real.log (L ^ 21),
          (33643 + 254231 / t) * t ^ 6 *
            Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t)) ≤
      0.00007 := by
  have hL0 : 0 < L := by linarith
  have hnu0 := (M6Certificate.sourceNu_sixth_bounds hL).1
  have hi := original_m5_finite_integral_envelope hL
  have hprice : 0 ≤ (12 / 5 : ℝ) * 37924 * 60 ^ 6 *
      Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) := by positivity
  have hi' :
      (∫ t in Real.log (10 * Real.pi * L ^ 7)..Real.log (L ^ 21),
        (33643 + 254231 / t) * t ^ 6 *
          Real.exp (-(14 / 15 : ℝ) * t - 0.478 * L / t)) ≤
      (12 / 5 : ℝ) * 37924 * 60 ^ 6 *
        Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
        Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7)) :=
    hi.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) hprice)
  have hn := mul_le_mul_of_nonneg_left (m5_nu_scaling hL)
    (show 0 ≤ L ^ (39 / 10 : ℝ) *
      Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
      Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7)) by positivity)
  calc
    _ ≤ (5 * L ^ (39 / 10 : ℝ) * sourceNu (L ^ 6)) *
        ((12 / 5 : ℝ) * 37924 * 60 ^ 6 *
          Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
          Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7))) :=
      mul_le_mul_of_nonneg_left hi' (by positivity)
    _ = (12 * 37924 * 60 ^ 6 : ℝ) *
        (L ^ (39 / 10 : ℝ) * sourceNu (L ^ 6) *
          Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
          Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7))) := by ring
    _ ≤ (12 * 37924 * 60 ^ 6 : ℝ) *
        (L ^ (39 / 10 : ℝ) * (7.56 * (L / 3100)) *
          Real.exp (-6 - 49.69 * Real.sqrt (L / 3100)) *
          Real.exp (-(5 / 12 : ℝ) * Real.log (10 * Real.pi * L ^ 7))) := by
      nlinarith only [hn]
    _ = (12 * 37924 * 60 ^ 6 * 7.56 / 3100 : ℝ) *
        Real.exp ((119 / 60 : ℝ) * Real.log L -
          (5 / 12 : ℝ) * Real.log (10 * Real.pi) -
          6 - 49.69 * Real.sqrt (L / 3100)) := by
      rw [m5_scalar_factor_identity hL0]
      ring
    _ ≤ (12 * 37924 * 60 ^ 6 * 7.56 / 3100 : ℝ) * Real.exp (-41.16) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (m5_scalar_exponent hL)) (by norm_num)
    _ ≤ _ := m5_scalar_rational_certificate

#print axioms original_m5_scalar_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
