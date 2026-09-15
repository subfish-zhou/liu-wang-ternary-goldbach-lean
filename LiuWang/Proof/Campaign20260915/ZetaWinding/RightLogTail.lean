import LiuWang.Proof.Campaign20260915.ZetaWinding.LogKernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.DirichletZeroCount.Remainder

theorem zeta_sub_one_decay {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ (3 / 4 : ℝ) * 2 ^ (2 - s.re) := by
  have hs1 : 1 < s.re := by linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs1
  have ht := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 2).mpr hsum
  have he : riemannZeta s - 1 = ∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs1]
    have hh := hsum.sum_add_tsum_nat_add 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
      zero_cpow (Complex.ne_zero_of_one_lt_re hs1), div_zero, Nat.cast_one,
      one_cpow, div_one, zero_add] at hh
    rw [← hh]
    ring
  have hb (n : ℕ) :
      ‖1 / ((n + 2 : ℕ) : ℂ) ^ s‖ ≤
        2 ^ (2 - s.re) * ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
    rw [norm_div, norm_one, norm_natCast_cpow_of_pos (by omega)]
    rw [one_div, ← Real.rpow_neg (by positivity)]
    calc
      _ = ((n + 2 : ℕ) : ℝ) ^ (2 - s.re) *
          ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast (show 2 ≤ n + 2 by omega))
          (by linarith)) (Real.rpow_nonneg (by positivity) _)
  have hreal : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 2).mpr
      (Real.summable_nat_rpow.mpr (by norm_num))
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, ‖1 / ((n + 2 : ℕ) : ℂ) ^ s‖ := norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' n : ℕ, 2 ^ (2 - s.re) * ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) :=
      ht.norm.tsum_le_tsum hb (hreal.mul_left _)
    _ = 2 ^ (2 - s.re) * ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-2 : ℝ) :=
      tsum_mul_left
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left square_tail_le
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 - s.re))
      simpa [mul_comm] using h

theorem norm_log_zeta_decay {s : ℂ} (hs : 2 ≤ s.re) :
    ‖log (riemannZeta s)‖ ≤ 3 * 2 ^ (2 - s.re) := by
  have hsmall : ‖riemannZeta s - 1‖ ≤ 3 / 4 := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      norm_LFunction_sub_one_le (1 : LiuWang.Proof.Interfaces.Character 1) hs
  have hl := norm_log_one_add_le (by linarith : ‖riemannZeta s - 1‖ < 1)
  have hi : (1 - ‖riemannZeta s - 1‖)⁻¹ ≤ (4 : ℝ) := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    linarith
  have hsq : ‖riemannZeta s - 1‖ ^ 2 ≤ ‖riemannZeta s - 1‖ := by
    nlinarith [norm_nonneg (riemannZeta s - 1)]
  have hm := mul_le_mul_of_nonneg_left hi (sq_nonneg ‖riemannZeta s - 1‖)
  have he := zeta_sub_one_decay hs
  have hid : 1 + (riemannZeta s - 1) = riemannZeta s := by ring
  rw [hid] at hl
  nlinarith

theorem log_tail_envelope_integrable (a : ℝ) :
    IntegrableOn (fun x : ℝ => (3 : ℝ) * 2 ^ (2 - x)) (Set.Ioi a) := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he (x : ℝ) : (3 : ℝ) * 2 ^ (2 - x) =
      12 * Real.exp (-Real.log 2 * x) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_two,
      Real.rpow_def_of_pos (by norm_num), div_eq_mul_inv, ← Real.exp_neg]
    norm_num [neg_mul]
    ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hp) a).const_mul 12

theorem integral_log_tail_envelope (a : ℝ) :
    (∫ x in Set.Ioi a, (3 : ℝ) * 2 ^ (2 - x)) =
      3 * 2 ^ (2 - a) / Real.log 2 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he (x : ℝ) : (3 : ℝ) * 2 ^ (2 - x) =
      12 * Real.exp (-Real.log 2 * x) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_two,
      Real.rpow_def_of_pos (by norm_num), div_eq_mul_inv, ← Real.exp_neg]
    norm_num [neg_mul]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hp) a]
  ring

theorem log_zeta_right_integrable (T : ℝ) {a : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun x => log (riemannZeta (horizontalAt T x))) (Set.Ioi a) := by
  have hc : ContinuousOn (fun x => log (riemannZeta (horizontalAt T x))) (Set.Ioi a) := by
    intro x hx
    have hz : 0 < (riemannZeta (horizontalAt T x)).re := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using
        LFunction_re_pos (1 : LiuWang.Proof.Interfaces.Character 1)
          (s := horizontalAt T x) (by simpa [horizontalAt] using ha.trans hx.le)
    have hn : horizontalAt T x ≠ 1 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp [horizontalAt] at hr
      linarith [show a < x from hx]
    have hc := ((hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inl hz))).continuousAt).comp
      (differentiableAt_riemannZeta hn).continuousAt
    exact (hc.comp (show ContinuousAt (horizontalAt T) x by
      unfold horizontalAt; fun_prop)).continuousWithinAt
  apply (log_tail_envelope_integrable a).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero] using
    norm_log_zeta_decay (s := horizontalAt T x) (by simpa [horizontalAt] using ha.trans hx.le)

theorem norm_integral_log_zeta_right_le (T : ℝ) {a : ℝ} (ha : 2 ≤ a) :
    ‖∫ x in Set.Ioi a, log (riemannZeta (horizontalAt T x))‖ ≤
      3 * 2 ^ (2 - a) / Real.log 2 := by
  rw [← integral_log_tail_envelope a]
  apply norm_integral_le_of_norm_le (log_tail_envelope_integrable a)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [horizontalAt, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero] using
    norm_log_zeta_decay (s := horizontalAt T x) (by simpa [horizontalAt] using ha.trans hx.le)

#print axioms zeta_sub_one_decay
#print axioms log_zeta_right_integrable
#print axioms norm_integral_log_zeta_right_le

end LiuWang.Proof.Campaign20260915.ZetaWinding
