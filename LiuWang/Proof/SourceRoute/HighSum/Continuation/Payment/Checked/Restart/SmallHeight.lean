import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.CountScalar
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Residual

/-! # The actual small-height branch of (2.25), including its signed alpha integral -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

theorem log_700000_upper : Real.log (700000 : ℝ) ≤ 14 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
    ((by norm_num : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le) 14
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

theorem small_height_gate {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y)
    (hyq : y ≤ max (100000 / (q : ℝ)) (10000 * Real.log q)) :
    700000 ≤ q ∧ max (100000 / (q : ℝ)) (10000 * Real.log q) =
      10000 * Real.log q := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hp := original_product_ge hN hy
  have hnot : ¬ y ≤ 100000 / (q : ℝ) := by
    intro h
    have hh := (le_div_iff₀ hq0).mp h
    nlinarith
  have hylog : y ≤ 10000 * Real.log q := (le_max_iff.mp hyq).resolve_left hnot
  have hq : 700000 ≤ q := by
    by_contra h
    have hqr : (q : ℝ) ≤ 700000 := by exact_mod_cast (show q ≤ 700000 by omega)
    have hl : Real.log q ≤ 14 := (Real.log_le_log hq0 hqr).trans log_700000_upper
    have h1 := mul_le_mul_of_nonneg_left hylog hq0.le
    have h2 := mul_le_mul_of_nonneg_left hl hq0.le
    nlinarith
  refine ⟨hq, max_eq_right ?_⟩
  exact (lt_of_not_ge hnot).le.trans hylog

theorem actual_source25 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha y : ℝ} (ha : 0 ≤ alpha) (hy : omegaCutoff N q ≤ y) :
    (familyCount q alpha y : ℝ) ≤ (q.totient : ℝ) *
      (y / Real.pi * Real.log ((q : ℝ) * y) - 0.874 * y +
        6.8423 * Real.log ((q : ℝ) * y) + 15) :=
  familyCount_le_source25 ha
    ((Parameters.omegaCutoff_ge (NeZero.pos q) hq).trans hy)
    (original_log_product_ge_ten hN hy)

theorem integral_layerKernel {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (a b : ℝ) :
    (∫ alpha in a..b, layerKernel N alpha) =
      Real.exp (sourceL N * (b - 1)) - Real.exp (sourceL N * (a - 1)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Parameters.nat_pos_of_exp_le hN)
  have hL : sourceL N ≠ 0 := ne_of_gt (by linarith [Parameters.sourceL_ge_3100 hN])
  unfold layerKernel
  simp_rw [Real.rpow_def_of_pos hn]
  change (∫ alpha in a..b, Real.exp (sourceL N * (alpha - 1)) * sourceL N) = _
  rw [intervalIntegral.integral_mul_const, integral_exp_shift a b hL, div_mul_cancel₀ _ hL]

theorem actual_source25_alpha_signed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      (q.totient : ℝ) * source25Bound q y *
        (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
          Real.exp (-sourceL N / 20)) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hb := original_alpha_cutoff_mem hN hy
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hi := (family_alpha_integrable (q := q) hn y).mono_set
    (show Set.uIcc (19 / 20 : ℝ) (1 - 0.478 / Real.log ((q : ℝ) * y)) ⊆
      Set.uIcc (19 / 20 : ℝ) 1 by
      rw [Set.uIcc_of_le hb.1, Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc le_rfl hb.2)
  calc
    _ ≤ ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * ((q.totient : ℝ) * source25Bound q y) := by
      apply intervalIntegral.integral_mono_on hb.1 hi
        (((continuous_layerKernel hn).mul continuous_const).intervalIntegrable _ _)
      intro alpha ha
      apply mul_le_mul_of_nonneg_left (actual_source25 hN hq (by linarith [ha.1]) hy)
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_layerKernel hN]
      have he : sourceL N * (1 - 0.478 / Real.log ((q : ℝ) * y) - 1) =
          -0.478 * sourceL N / Real.log ((q : ℝ) * y) := by ring
      rw [he, show sourceL N * ((19 / 20 : ℝ) - 1) = -sourceL N / 20 by ring]
      ring

theorem source25Bound_nonneg {q : ℕ} [NeZero q] {y : ℝ}
    (hy : 3.36 ≤ y) (hs : 10 ≤ Real.log ((q : ℝ) * y)) :
    0 ≤ source25Bound q y :=
  (Nat.cast_nonneg (count (1 : Character q) 0 y)).trans
    (count_le_source25 (1 : Character q) le_rfl hy hs)

theorem actual_source25_alpha {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      (q.totient : ℝ) * source25Bound q y *
        Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) := by
  have hb := source25Bound_nonneg
    ((Parameters.omegaCutoff_ge (NeZero.pos q) hq).trans hy)
    (original_log_product_ge_ten hN hy)
  exact (actual_source25_alpha_signed hN hq hy).trans
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le)
      (mul_nonneg (Nat.cast_nonneg _) hb))

theorem unpaidAlpha_small_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    unpaidAlpha N q y ≤
      (q.totient : ℝ) * source25Bound q y *
        (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
          Real.exp (-sourceL N / 20)) +
      lambdaCountSegment N q y 0 0.36 := by
  rw [unpaidAlpha_eq_original_ranges hN hy]
  linarith [actual_source25_alpha_signed hN hq hy]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
