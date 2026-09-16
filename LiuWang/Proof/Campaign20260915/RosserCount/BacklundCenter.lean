import LiuWang.Proof.Campaign20260915.RosserCount.OriginalRemainder
import LiuWang.Proof.Campaign20260915.ZetaWinding.PositiveCount

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter
open scoped Topology ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.RosserCount

def backlundCenterPoint (T : ℝ) : ℂ := 5 / 4 + (T : ℂ) * I

def backlundAux (T : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta (s + 5 / 4 + (T : ℂ) * I) ^ n +
    riemannZeta (s + 5 / 4 - (T : ℂ) * I) ^ n) / 2

theorem backlundCenter_nonzero (T : ℝ) :
    riemannZeta (backlundCenterPoint T) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by norm_num [backlundCenterPoint])

theorem backlundAux_zero (T : ℝ) (n : ℕ) :
    backlundAux T n 0 = ((riemannZeta (backlundCenterPoint T) ^ n).re : ℂ) := by
  have hc : riemannZeta (5 / 4 - (T : ℂ) * I) =
      conj (riemannZeta (backlundCenterPoint T)) := by
    rw [← riemannZeta_conj]
    congr 1
    simp [backlundCenterPoint, sub_eq_add_neg, conj_ofNat]
  apply Complex.ext <;>
    simp [backlundAux, hc, ← map_pow, backlundCenterPoint]

theorem exists_power_large_real_part (z : ℂ) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ 2 * n ∧ ‖z ^ m‖ / 2 ≤ |(z ^ m).re| := by
  by_cases h : ‖z ^ n‖ / 2 ≤ |(z ^ n).re|
  · exact ⟨n, le_rfl, by omega, h⟩
  · refine ⟨2 * n, by omega, le_rfl, ?_⟩
    let w := z ^ n
    have hw : |w.re| < ‖w‖ / 2 := lt_of_not_ge h
    have hs := Complex.sq_norm_sub_sq_re w
    have hr : w.re ^ 2 ≤ ‖w‖ ^ 2 / 4 := by
      nlinarith [sq_abs w.re, abs_nonneg w.re, norm_nonneg w]
    have he : z ^ (2 * n) = w ^ 2 := by
      dsimp [w]
      rw [Nat.mul_comm, pow_mul]
    rw [he]
    have hp : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
      simp [pow_two, Complex.mul_re]
    calc
      ‖w ^ 2‖ / 2 ≤ -(w ^ 2).re := by rw [norm_pow, hp]; nlinarith
      _ ≤ |(w ^ 2).re| := neg_le_abs _

theorem large_real_part_log_bound {z : ℂ} (hz : z ≠ 0) {n m : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (hm : ‖z ^ m‖ / 2 ≤ |(z ^ m).re|) :
    |Real.log |(z ^ m).re| / (m : ℝ) - Real.log ‖z‖| ≤ Real.log 2 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hn hnm)
  have hp : 0 < ‖z ^ m‖ := norm_pos_iff.mpr (pow_ne_zero _ hz)
  have hr : 0 < |(z ^ m).re| := (half_pos hp).trans_le hm
  have hlo := Real.log_le_log (half_pos hp) hm
  rw [Real.log_div hp.ne' (by norm_num), norm_pow, Real.log_pow] at hlo
  have hhi := Real.log_le_log hr (Complex.abs_re_le_norm (z ^ m))
  rw [norm_pow, Real.log_pow] at hhi
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have habs : |Real.log |(z ^ m).re| - (m : ℝ) * Real.log ‖z‖| ≤ Real.log 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have he : Real.log |(z ^ m).re| / (m : ℝ) - Real.log ‖z‖ =
      (Real.log |(z ^ m).re| - (m : ℝ) * Real.log ‖z‖) / (m : ℝ) := by
    field_simp
  rw [he, abs_div, abs_of_pos hm0]
  exact (div_le_div_of_nonneg_right habs hm0.le).trans
    (div_le_div_of_nonneg_left hlog hn0 (by exact_mod_cast hnm))

theorem backlundAux_center_power_bound (T : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ 2 * n ∧ backlundAux T m 0 ≠ 0 ∧
      |Real.log ‖backlundAux T m 0‖ / (m : ℝ) -
        Real.log ‖riemannZeta (backlundCenterPoint T)‖| ≤ Real.log 2 / (n : ℝ) := by
  obtain ⟨m, hnm, hmn, hm⟩ := exists_power_large_real_part
    (riemannZeta (backlundCenterPoint T)) n
  have hz := backlundCenter_nonzero T
  have hp : 0 < |(riemannZeta (backlundCenterPoint T) ^ m).re| :=
    (half_pos (norm_pos_iff.mpr (pow_ne_zero _ hz))).trans_le hm
  refine ⟨m, hnm, hmn, ?_, ?_⟩
  · rw [backlundAux_zero]
    exact_mod_cast (abs_pos.mp hp)
  · simpa only [backlundAux_zero, Complex.norm_real, Real.norm_eq_abs] using
      large_real_part_log_bound hz hn hnm hm

theorem backlundAux_center_log_limit (T : ℝ) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      (∀ n, backlundAux T (f n) 0 ≠ 0) ∧
      Tendsto (fun n => Real.log ‖backlundAux T (f n) 0‖ / (f n : ℝ))
        atTop (𝓝 (Real.log ‖riemannZeta (backlundCenterPoint T)‖)) := by
  choose f hf using fun n => backlundAux_center_power_bound T (Nat.succ_pos n)
  have htop : Tendsto f atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (hf n).1) tendsto_id
  refine ⟨f, htop, fun n => (hf n).2.2.1, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hb : Tendsto (fun n : ℕ => Real.log 2 / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_zero] using hi.const_mul (Real.log 2)
  apply squeeze_zero (fun n => norm_nonneg _) ?_ hb
  intro n
  simpa only [Real.norm_eq_abs] using (hf n).2.2.2

#print axioms backlundCenter_nonzero
#print axioms backlundAux_zero
#print axioms exists_power_large_real_part
#print axioms large_real_part_log_bound
#print axioms backlundAux_center_power_bound
#print axioms backlundAux_center_log_limit

end LiuWang.Proof.Campaign20260915.RosserCount
