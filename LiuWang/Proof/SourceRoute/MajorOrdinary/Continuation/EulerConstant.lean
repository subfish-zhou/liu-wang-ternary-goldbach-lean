import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.Nu

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

def correctedHarmonic (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1 / (2 * (n : ℝ)) + 1 / (12 * (n : ℝ) ^ 2)

theorem corrected_log_step {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) - 1 / (2 * (x + 1)) + 1 / (2 * x) +
        1 / (12 * (x + 1) ^ 2) - 1 / (12 * x ^ 2) ≤
      Real.log (x + 1) - Real.log x := by
  have hz0 : 0 ≤ 1 / (2 * x + 1) := by positivity
  have hz1 : 1 / (2 * x + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have h := Real.sum_range_le_log_div hz0 hz1 2
  have he : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp
    ring
  rw [he, Real.log_div (by positivity) hx.ne'] at h
  norm_num [Finset.sum_range_succ] at h
  have hr :
      1 / (x + 1) - 1 / (2 * (x + 1)) + 1 / (2 * x) +
          1 / (12 * (x + 1) ^ 2) - 1 / (12 * x ^ 2) ≤
        2 * (1 / (2 * x + 1) + (1 / (2 * x + 1)) ^ 3 / 3) := by
    field_simp
    nlinarith [sq_nonneg x]
  simp only [one_div, inv_pow] at hr
  simp only [one_div]
  linarith

theorem correctedHarmonic_step {n : ℕ} (hn : 0 < n) :
    correctedHarmonic (n + 1) ≤ correctedHarmonic n := by
  have h := corrected_log_step (Nat.cast_pos.mpr hn)
  simp only [correctedHarmonic, harmonic_succ, Rat.cast_add, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  simp only [one_div] at h ⊢
  linarith

theorem correctedHarmonic_limit :
    Tendsto correctedHarmonic atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he (n : ℕ) :
      correctedHarmonic n = ((harmonic n : ℝ) - Real.log n) -
        (1 / 2) * (n : ℝ)⁻¹ + (1 / 12) * ((n : ℝ)⁻¹) ^ 2 := by
    unfold correctedHarmonic
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  simp only [funext he]
  simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero, one_div] using
    (Real.tendsto_harmonic_sub_log.sub (h.const_mul (2 : ℝ)⁻¹)).add
    ((h.pow 2).const_mul (12 : ℝ)⁻¹)

theorem gamma_le_correctedHarmonic {n : ℕ} (hn : 0 < n) :
    Real.eulerMascheroniConstant ≤ correctedHarmonic n := by
  apply le_of_tendsto correctedHarmonic_limit
  filter_upwards [eventually_ge_atTop n] with m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => exact (correctedHarmonic_step (hn.trans_le hm)).trans ih

theorem gamma_le_decimal : Real.eulerMascheroniConstant ≤ 0.577217 := by
  have h := gamma_le_correctedHarmonic (n := 10) (by norm_num)
  have hl : 2.3025850926 ≤ Real.log (10 : ℝ) := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  norm_num [correctedHarmonic] at h
  linarith

theorem exp_gamma_le_decimal : Real.exp Real.eulerMascheroniConstant ≤ 1.781076 := by
  apply (Real.exp_le_exp.mpr gamma_le_decimal).trans
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.577217)
    (by norm_num : (0.577217 : ℝ) ≤ 1) (n := 10) (by norm_num)
  apply h.trans
  norm_num [Finset.sum_range_succ, Nat.factorial]

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
