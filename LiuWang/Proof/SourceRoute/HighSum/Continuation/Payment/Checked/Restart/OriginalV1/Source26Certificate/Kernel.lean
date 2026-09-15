import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Consumer
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.RationalExp

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate

def integrand (L s : ℝ) : ℝ :=
  Real.exp (-s) *
    ((17102 + 254231 / s) * s ^ (6 : ℕ) * L ^ (5 : ℕ) / (L - 4 * s) *
        Real.exp (-0.478 * (L - 4 * s) / s) +
      16541 * s ^ (6 : ℕ) * L ^ (4 : ℕ) * Real.exp (-0.478 * L / s))

def scalar (L : ℝ) : ℝ :=
  ∫ s in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (L ^ (3 : ℕ) * L ^ (15 : ℕ)),
    integrand L s

theorem scalar_literal (L : ℝ) :
    scalar L =
      ∫ s in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (L ^ (3 : ℕ) * L ^ (15 : ℕ)),
        Real.exp (-s) *
          ((17102 + 254231 / s) * s ^ (6 : ℕ) * L ^ (5 : ℕ) / (L - 4 * s) *
              Real.exp (-0.478 * (L - 4 * s) / s) +
            16541 * s ^ (6 : ℕ) * L ^ (4 : ℕ) * Real.exp (-0.478 * L / s)) := rfl

theorem integrand_factor (L : ℝ) {s : ℝ} (hs : s ≠ 0) :
    integrand L s =
      s ^ (6 : ℕ) * Real.exp (-s) *
        ((17102 + 254231 / s) * (L / (L - 4 * s)) * Real.exp 1.912 + 16541) *
        (L ^ (4 : ℕ) * Real.exp (-(0.478 / s) * L)) := by
  have he : -0.478 * (L - 4 * s) / s = 1.912 + -(0.478 / s) * L := by
    field_simp
    ring
  unfold integrand
  rw [he, Real.exp_add, show -0.478 * L / s = -(0.478 / s) * L by ring]
  ring

theorem power_exp_le {x y c : ℝ} (n : ℕ) (hx : 0 < x) (hxy : x ≤ y)
    (hc : (n : ℝ) ≤ c * x) :
    y ^ n * Real.exp (-c * y) ≤ x ^ n * Real.exp (-c * x) := by
  have hy := hx.trans_le hxy
  have hr : 1 ≤ y / x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have hnlog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hmul := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hr)
  have he : (n : ℝ) * Real.log (y / x) - c * y ≤ -c * x := by
    have hh := hnlog.trans hmul
    have hid : c * x * (y / x - 1) = c * y - c * x := by field_simp
    rw [hid] at hh
    linarith
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (div_pos hy hx)] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hx.le n)
  rw [show -c * y = -(c * y) by ring, Real.exp_neg]
  calc
    _ = x ^ n * ((y / x) ^ n / Real.exp (c * y)) := by
      rw [div_pow]
      field_simp
    _ ≤ _ := hh'

theorem exp_1912_upper : Real.exp (1.912 : ℝ) ≤ 6.77 := by
  have h := Real.exp_bound' (x := (0.912 : ℝ)) (by norm_num) (by norm_num)
    (n := 9) (by norm_num)
  have he : Real.exp (0.912 : ℝ) ≤ 2.49 := by
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hh := mul_le_mul Real.exp_one_lt_d9.le he (Real.exp_pos _).le (by norm_num)
  rw [← Real.exp_add] at hh
  norm_num at hh
  linarith

theorem integrand_nonneg {L s : ℝ} (hL : 3100 ≤ L) (hs : 0 < s)
    (hsL : s ≤ 18 * Real.log L) : 0 ≤ integrand L s := by
  have hd := source26_denominator hL hsL
  unfold integrand
  positivity

theorem integrand_integrable {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 18 * Real.log L) :
    IntervalIntegrable (integrand L) volume a b := by
  change IntervalIntegrable (fun s => integrand L s) volume a b
  simp_rw [integrand, ← source26_normalization, mul_assoc]
  exact
    (source26_log_integrable hL ha hab hb).const_mul (L ^ (4 : ℕ))

theorem integrand_le_base {L s : ℝ} (hL : 3100 ≤ L)
    (hs : 0 < s) (hs100 : s ≤ 100) :
    integrand L s ≤ integrand 3100 s := by
  have hL0 : 0 < L := by linarith
  have hd0 : 0 < 3100 - 4 * s := by linarith
  have hd : 0 < L - 4 * s := by linarith
  have hratio : L / (L - 4 * s) ≤ 3100 / (3100 - 4 * s) := by
    apply (div_le_div_iff₀ hd hd0).mpr
    nlinarith
  have hc : (4 : ℝ) ≤ (0.478 / s) * 3100 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hs).mpr
    linarith
  have hp := power_exp_le 4 (by norm_num : (0 : ℝ) < 3100) hL hc
  rw [integrand_factor L hs.ne', integrand_factor 3100 hs.ne']
  have hcoeff :
      (17102 + 254231 / s) * (L / (L - 4 * s)) * Real.exp 1.912 + 16541 ≤
      (17102 + 254231 / s) * (3100 / (3100 - 4 * s)) * Real.exp 1.912 + 16541 := by
    gcongr
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hcoeff (by positivity)) hp (by positivity) (by positivity)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Certificate
