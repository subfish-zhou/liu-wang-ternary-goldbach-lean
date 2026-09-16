import LiuWang.Proof.Campaign20260915.RosserCount.BacklundFixedRightCircle
import LiuWang.Proof.Campaign20260915.ZetaValidation.Logarithm64

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.Campaign20260915.ZetaValidation

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundExpLower (q : ℚ) : ℚ :=
  ∑ k ∈ range 25, q ^ k / k.factorial

theorem backlundExpLower_le_exp {q : ℚ} (hq : 0 ≤ q) :
    (backlundExpLower q : ℝ) ≤ Real.exp (q : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (Rat.cast_nonneg.mpr hq) 25
  simpa only [backlundExpLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast] using h

theorem backlund_rpow_div_certificate {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 64)
    {a q d u : ℚ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hd : 0 < d) (hu : 0 ≤ u)
    (hql : q ≤ a * (logNaturalCenter n - 1 / 1000000))
    (hpoly : 1 ≤ d * u * backlundExpLower q) :
    (n : ℝ) ^ (-(a : ℝ)) / (d : ℝ) ≤ (u : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl := (abs_le.mp (logNaturalCenter_error hn hn')).1
  have haR : (0 : ℝ) ≤ a := Rat.cast_nonneg.mpr ha
  have hdR : (0 : ℝ) < d := Rat.cast_pos.mpr hd
  have huR : (0 : ℝ) ≤ u := Rat.cast_nonneg.mpr hu
  have hqR : (q : ℝ) ≤ (a : ℝ) * (Real.log n) := by
    have h : (q : ℝ) ≤ (a : ℝ) * ((logNaturalCenter n : ℝ) - 1 / 1000000) := by
      simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le.mpr hql : (q : ℝ) ≤ ((a * (logNaturalCenter n - 1 / 1000000) : ℚ) : ℝ))
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) haR)
  have he := (backlundExpLower_le_exp hq).trans (Real.exp_le_exp.mpr hqR)
  have hp : (1 : ℝ) ≤ (d : ℝ) * (u : ℝ) * Real.exp ((a : ℝ) * Real.log n) := by
    have hh : (1 : ℝ) ≤ (d : ℝ) * (u : ℝ) * (backlundExpLower q : ℝ) := by
      exact_mod_cast hpoly
    exact hh.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hdR.le huR))
  have hr : (n : ℝ) ^ (-(a : ℝ)) ≤ (d : ℝ) * (u : ℝ) := by
    rw [Real.rpow_def_of_pos hn0,
      show Real.log (n : ℝ) * -(a : ℝ) = -((a : ℝ) * Real.log n) by ring,
      Real.exp_neg, inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith)
  exact (div_le_iff₀ hdR).mpr (by nlinarith)

theorem backlund_log_certificate {x : ℝ} (hx : 0 < x) {v q : ℚ}
    (hv : x ≤ (v : ℝ)) (hq : 0 ≤ q) (hp : v ≤ backlundExpLower q) :
    Real.log x ≤ (q : ℝ) := by
  have hpR : (v : ℝ) ≤ (backlundExpLower q : ℝ) := Rat.cast_le.mpr hp
  exact (Real.log_le_iff_le_exp hx).mpr
    (hv.trans (hpR.trans (backlundExpLower_le_exp hq)))

#print axioms backlundExpLower_le_exp
#print axioms backlund_rpow_div_certificate
#print axioms backlund_log_certificate

end LiuWang.Proof.Campaign20260915.RosserCount
