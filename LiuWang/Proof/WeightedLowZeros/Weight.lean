import LiuWang.Proof.OscillatoryBounds.Main
import LiuWang.Proof.Parameters.Main

/-! # The literal Lemma 2.1 weight, with its original-window normalization -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.WeightedLowZeros

def weight (N : ℕ) (beta : ℝ) : ℝ :=
  (1 - (0.001 : ℝ) ^ beta) / beta * (N : ℝ) ^ (beta - 1)

theorem weight_nonneg (N : ℕ) {beta : ℝ} (hb : 0 < beta) :
    0 ≤ weight N beta := by
  have hpow : (0.001 : ℝ) ^ beta ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) hb.le
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr hpow) hb.le)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem weight_mul_endpoint {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    (N : ℝ) * weight N beta =
      (1 - (0.001 : ℝ) ^ beta) / beta * (N : ℝ) ^ beta := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  rw [weight, Real.rpow_sub_one hn]
  field_simp

theorem weight_eq_integral {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : 0 < beta) :
    weight N beta =
      (∫ t in (N : ℝ) / 1000..(N : ℝ), t ^ (beta - 1)) / (N : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [integral_rpow (Or.inl (by linarith : -1 < beta - 1))]
  simp only [sub_add_cancel]
  rw [show (N : ℝ) / 1000 = (0.001 : ℝ) * N by ring,
    Real.mul_rpow (by norm_num) hn.le, weight, Real.rpow_sub_one hn.ne']
  ring

theorem intervalIntegrable_weight_kernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (beta : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ (beta - 1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact fun t ht => (Real.continuousAt_rpow_const t (beta - 1)
    (Or.inl (ha.trans_le ht.1).ne')).continuousWithinAt

theorem weight_mono {N : ℕ} (hN : 1000 ≤ (N : ℝ)) {beta sigma : ℝ}
    (hb : 0 < beta) (hbs : beta ≤ sigma) : weight N beta ≤ weight N sigma := by
  have hn : 0 < N := Nat.cast_pos.mp (by linarith : (0 : ℝ) < N)
  have ha : 0 < (N : ℝ) / 1000 := by positivity
  have hab : (N : ℝ) / 1000 ≤ N := by linarith
  rw [weight_eq_integral hn hb, weight_eq_integral hn (hb.trans_le hbs)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply intervalIntegral.integral_mono_on hab
    (intervalIntegrable_weight_kernel ha hab beta)
    (intervalIntegrable_weight_kernel ha hab sigma)
  intro t ht
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by linarith)

theorem weight_one (N : ℕ) : weight N 1 = 0.999 := by
  norm_num [weight]

theorem weight_le_one {N : ℕ} (hN : 1000 ≤ (N : ℝ)) {beta : ℝ}
    (hb : 0 < beta) (hb1 : beta ≤ 1) : weight N beta ≤ 0.999 := by
  simpa only [weight_one] using weight_mono hN hb hb1

theorem Jrho_le_weight {N : ℕ} (hN : 0 < N) {rho : ℂ}
    (hb : 0 < rho.re) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ (N : ℝ) * weight N rho.re := by
  rw [weight_mul_endpoint hN]
  exact OscillatoryBounds.norm_integral_cpow_charReal_le_source_weight
    (Nat.cast_pos.mpr hN) hb eta

theorem source_endpoint_ge_thousand {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) : 1000 ≤ (N : ℝ) := by
  have h := Parameters.mul_sourceL_pow_lt (k := 0) (c := 1000)
    (Parameters.exp_2000_le_of_exp_3100_le hN) (by norm_num) (by norm_num)
  simpa using h.le

end LiuWang.Proof.WeightedLowZeros
