import LiuWang.Proof.NonprincipalDensityAdvance.Detector

/-! # Uniform right-boundary payment for actual character detectors -/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NonprincipalDensityAdvance

theorem norm_twistedMu_term_le {q : ℕ} (chi : Character q)
    {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖LSeries.term (twistedMu chi) s n‖ ≤ (n : ℝ) ^ (-s.re) := by
  apply le_trans (LSeries.norm_term_le (g := fun k => (ArithmeticFunction.moebius k : ℂ))
    s (show ‖twistedMu chi n‖ ≤
    ‖(ArithmeticFunction.moebius n : ℂ)‖ by
      rw [twistedMu, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (chi.norm_le_one n)))
  exact GlobalZeroDensity.norm_mu_term_le hs n

theorem norm_LFunction_le {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 1 < s.re) : ‖chi.LFunction s‖ ≤ 1 + 1 / (s.re - 1) := by
  have he : (s.re : ℂ) + Complex.I * s.im = s := by
    simpa only [mul_comm] using Complex.re_add_im s
  simpa only [he] using
    AnalyticNumberTheory.LargeSieve.norm_dirichletLFunction_le chi s.re s.im hs

theorem norm_f_le_right {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 1 < s.re) {X : ℝ} (hX : 1 < X) :
    ‖f chi X s‖ ≤ (1 + 1 / (s.re - 1)) *
      (((⌈X⌉₊ : ℝ) - 1) ^ (1 - s.re) / (s.re - 1)) := by
  have hmu : LSeriesSummable (twistedMu chi) s :=
    chi.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have htail := (summable_nat_add_iff ⌈X⌉₊).mpr hmu
  have hp : Summable (fun n : ℕ => ((n + ⌈X⌉₊ : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_nat_add_iff ⌈X⌉₊).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  rw [f_eq_moebius_tail chi hs X, norm_mul, norm_neg]
  apply mul_le_mul (norm_LFunction_le chi hs) _ (norm_nonneg _) (by positivity)
  exact (norm_tsum_le_tsum_norm htail.norm).trans
    ((htail.norm.tsum_le_tsum (fun n => norm_twistedMu_term_le chi hs _) hp).trans
      (GlobalZeroDensity.rpow_tail_le hs hN))

theorem norm_f_two_le {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : s.re = 2) {X : ℝ} (hX : 1 < X) :
    ‖f chi X s‖ ≤ 2 / (X - 1) := by
  have ht := norm_f_le_right chi (s := s) (by rw [hs]; norm_num) hX
  have he : (1 + 1 / (s.re - 1)) *
      (((⌈X⌉₊ : ℝ) - 1) ^ (1 - s.re) / (s.re - 1)) =
      2 / ((⌈X⌉₊ : ℝ) - 1) := by
    rw [hs]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  rw [he] at ht
  exact ht.trans (div_le_div_of_nonneg_left (by norm_num)
    (by linarith) (by linarith [Nat.le_ceil X]))

theorem H_ne_zero_on_two {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : s.re = 2) {X : ℝ} (hX : 3 < X) : H chi X s ≠ 0 := by
  have hf : ‖f chi X s‖ < 1 :=
    (norm_f_two_le chi hs (by linarith)).trans_lt
      ((div_lt_one (by linarith)).mpr (by linarith))
  intro hz
  have hp : f chi X s ^ 2 = 1 := (sub_eq_zero.mp hz).symm
  have hn := congrArg norm hp
  rw [norm_pow, norm_one] at hn
  nlinarith [norm_nonneg (f chi X s)]

theorem abs_log_norm_one_sub_sq_le {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 2) :
    |Real.log ‖1 - z ^ 2‖| ≤ 2 * ‖z‖ ^ 2 := by
  have hlo : 1 - ‖z‖ ^ 2 ≤ ‖1 - z ^ 2‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    rw [norm_one, norm_pow] at h
    exact h
  have hhi : ‖1 - z ^ 2‖ ≤ 1 + ‖z‖ ^ 2 := by
    have h := norm_sub_le (1 : ℂ) (z ^ 2)
    rw [norm_one, norm_pow] at h
    exact h
  have hpos : 0 < ‖1 - z ^ 2‖ := by linarith
  have hinv : ‖1 - z ^ 2‖⁻¹ ≤ 1 + 2 * ‖z‖ ^ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have hm := mul_le_mul_of_nonneg_right hlo
      (by positivity : 0 ≤ 1 + 2 * ‖z‖ ^ 2)
    nlinarith [sq_nonneg ‖z‖]
  have hloglo := Real.one_sub_inv_le_log_of_pos hpos
  have hloghi := Real.log_le_sub_one_of_pos hpos
  exact abs_le.mpr ⟨by linarith, by nlinarith [sq_nonneg ‖z‖]⟩

theorem abs_log_H_two_le {q : ℕ} [NeZero q] (chi : Character q)
    {X : ℝ} (hX : 5 ≤ X) {s : ℂ} (hs : s.re = 2) :
    |Real.log ‖H chi X s‖| ≤ 8 / (X - 1) ^ 2 := by
  have hf := norm_f_two_le chi hs (by linarith : 1 < X)
  have hb : 2 / (X - 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < X - 1)).mpr
    linarith
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hsmall : ‖f chi X s‖ ^ 2 ≤ 1 / 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hf.trans hb) 2
    norm_num at hh
    linarith
  calc
    _ ≤ 2 * ‖f chi X s‖ ^ 2 := abs_log_norm_one_sub_sq_le hsmall
    _ ≤ 2 * (2 / (X - 1)) ^ 2 := mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ = _ := by rw [div_pow]; norm_num; ring

theorem intervalIntegrable_log_H_two {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 3 < X) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖H chi X ((2 : ℂ) + t * Complex.I)‖)
      volume (-u) u := by
  have hv : Continuous (fun t : ℝ => (2 : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact (((differentiable_H hchi X).continuous.comp hv).norm.log
    (fun _ => norm_ne_zero_iff.mpr (H_ne_zero_on_two chi (by simp) hX))).intervalIntegrable _ _

theorem abs_log_integral_two_le {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {X : ℝ} (hX : 5 ≤ X) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in -u..u, |Real.log ‖H chi X ((2 : ℂ) + t * Complex.I)‖|) ≤
      16 * u / (X - 1) ^ 2 := by
  have hi := (intervalIntegrable_log_H_two hchi (by linarith : 3 < X) u).abs
  have hm := intervalIntegral.integral_mono_on (by linarith : -u ≤ u)
    hi (intervalIntegrable_const (c := 8 / (X - 1) ^ 2))
    (fun t _ => abs_log_H_two_le chi hX (by simp))
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  convert hm using 1
  ring

end LiuWang.Proof.NonprincipalDensityAdvance
