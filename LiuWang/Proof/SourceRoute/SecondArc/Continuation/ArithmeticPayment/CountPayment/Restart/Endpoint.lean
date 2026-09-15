import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.BandDomain

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart

theorem endpoint_tail_count_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ alpha in stripLower q (middleUpper N q)..1,
      alphaKernel (0.001 * (N : ℝ)) alpha *
        (familyCount q alpha (middleUpper N q) : ℝ)) ≤
      14000 * (1 - Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))) := by
  have hd := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hl := (middle_log_domain hN hq
    (show middleUpper N q ∈ Set.Icc (omegaCutoff N q) (middleUpper N q) from
      ⟨hd.2.1, le_rfl⟩)).2.1
  have hab : stripLower q (middleUpper N q) ≤ 1 := by
    unfold stripLower
    have hh : 0 ≤ 0.478 / Real.log ((q : ℝ) * middleUpper N q) := by positivity
    linarith
  calc
    _ ≤ ∫ alpha in stripLower q (middleUpper N q)..1,
        14000 * alphaKernel (0.001 * (N : ℝ)) alpha := by
      apply intervalIntegral.integral_mono_on hab (count_alpha_integrable hx hab _)
        (((continuous_alphaKernel hx).const_mul 14000).intervalIntegrable _ _)
      intro alpha ha
      have hk : 0 ≤ alphaKernel (0.001 * (N : ℝ)) alpha :=
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (window_base_ge_one hN))
      exact (mul_le_mul_of_nonneg_left
        (actual_familyCount_14000 hN hq hd.2.1 ha.1) hk).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_alphaKernel hx]
      simp only [sub_self, Real.rpow_zero, stripLower, sub_sub_cancel_left]
      rw [Real.rpow_def_of_pos hx, log_window_eq (nat_pos_of_exp_le hN),
        (source_log_endpoints (N := N) (q := q)).2]
      congr 3
      ring

theorem endpoint_normalization_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    140000 * (Real.sqrt q / q.totient) / Real.sqrt (middleUpper N q) ≤
      0.0004 / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hphi : (0 : ℝ) < q.totient :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hd := middle_height_domain hN hq
  have hv : 0 < middleUpper N q := hd.1.trans_le hd.2.1
  have hr := totient_ratio_le_source (NeZero.pos q) hL hq
  have hsq : Real.sqrt q * Real.sqrt (middleUpper N q) =
      Real.sqrt (10 * Real.pi) * sourceL N ^ (3 : ℕ) * Real.sqrt (sourceL N) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hq0.le, Real.sq_sqrt hv.le]
    have he : (q : ℝ) * middleUpper N q = 10 * Real.pi * sourceL N ^ (7 : ℕ) := by
      unfold middleUpper
      field_simp
    rw [he, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hLp.le]
    ring
  have hroot : 5.5 ≤ Real.sqrt (10 * Real.pi) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_d2])
  have hrootL : 55 ≤ Real.sqrt (sourceL N) :=
    (Real.le_sqrt (by norm_num) hLp.le).mpr (by linarith)
  have he : (Real.sqrt q / (q.totient : ℝ)) / Real.sqrt (middleUpper N q) =
      ((q : ℝ) / q.totient) /
        (Real.sqrt (10 * Real.pi) * sourceL N ^ (3 : ℕ) * Real.sqrt (sourceL N)) := by
    rw [← hsq]
    field_simp
    rw [Real.sq_sqrt hq0.le]
  rw [mul_div_assoc, he]
  have hden : 0 < Real.sqrt (10 * Real.pi) * sourceL N ^ (3 : ℕ) *
      Real.sqrt (sourceL N) := by positivity
  have hb : (5.5 * 55) * sourceL N ^ (3 : ℕ) ≤
      Real.sqrt (10 * Real.pi) * sourceL N ^ (3 : ℕ) * Real.sqrt (sourceL N) := by
    have hh := mul_le_mul hroot hrootL (by norm_num) (Real.sqrt_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ sourceL N ^ (3 : ℕ))
    nlinarith only [hm]
  have hh := div_le_div_of_nonneg_right hr hden.le
  apply (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 140000)).trans
  apply (le_div_iff₀ hLp).mpr
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 0.0004)
  have hp := mul_nonneg (by linarith : 0 ≤ 0.0004 * (5.5 * 55) * sourceL N - 140000 * 8 / 3100)
    (by positivity : 0 ≤ sourceL N ^ (2 : ℕ))
  nlinarith only [hm, hp]

theorem endpoint_tail_difference_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (10 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        ∫ alpha in stripLower q (middleUpper N q)..1,
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (familyCount q alpha (middleUpper N q) : ℝ)) ≤
      (0.0004 * (N : ℝ) / sourceL N) *
        (1 - Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))) := by
  have ht := endpoint_tail_count_integral hN hq
  have hd := middle_height_domain hN hq
  have hl := (middle_log_domain hN hq
    (show middleUpper N q ∈ Set.Icc (omegaCutoff N q) (middleUpper N q) from
      ⟨hd.2.1, le_rfl⟩)).2.1
  rw [(source_log_endpoints (N := N) (q := q)).2] at hl
  have hH : 0 ≤ sourceL N + Real.log 0.001 := by
    rw [← log_window_eq (nat_pos_of_exp_le hN)]
    exact Real.log_nonneg (window_base_ge_one hN)
  have he : 0 ≤ 1 - Real.exp (-0.478 * (sourceL N + Real.log 0.001) /
      Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ))) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hH)
      (by linarith)
  have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤
    (10 * (N : ℝ) * Real.sqrt q / q.totient) / Real.sqrt (middleUpper N q))
  have hp := mul_le_mul_of_nonneg_left (endpoint_normalization_bound hN hq) (Nat.cast_nonneg N)
  have hp' := mul_le_mul_of_nonneg_right hp he
  simp only [div_eq_mul_inv] at hh hp' ⊢
  nlinarith only [hh, hp']

theorem endpoint_tail_payment {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (10 * (N : ℝ) * Real.sqrt q / q.totient) *
      ((1 / Real.sqrt (middleUpper N q)) *
        ∫ alpha in stripLower q (middleUpper N q)..1,
          alphaKernel (0.001 * (N : ℝ)) alpha *
            (familyCount q alpha (middleUpper N q) : ℝ)) ≤
      0.0004 * (N : ℝ) / sourceL N := by
  have ht := endpoint_tail_count_integral hN hq
  have hle : (∫ alpha in stripLower q (middleUpper N q)..1,
      alphaKernel (0.001 * (N : ℝ)) alpha *
        (familyCount q alpha (middleUpper N q) : ℝ)) ≤ 14000 := by
    linarith [Real.exp_pos (-0.478 * (sourceL N + Real.log 0.001) /
      Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)))]
  have hh := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤
    (10 * (N : ℝ) * Real.sqrt q / q.totient) / Real.sqrt (middleUpper N q))
  have hp := mul_le_mul_of_nonneg_left (endpoint_normalization_bound hN hq) (Nat.cast_nonneg N)
  simp only [div_eq_mul_inv] at hh hp ⊢
  nlinarith only [hh, hp]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
