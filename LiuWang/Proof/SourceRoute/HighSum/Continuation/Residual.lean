import LiuWang.Proof.SourceRoute.HighSum.Continuation.LogHeight

/-! # Reattach the paid contribution without deleting the unpaid alpha ranges -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation

def unpaidAlpha (N q : ℕ) [NeZero q] (y : ℝ) : ℝ :=
  (∫ alpha in (19 / 20 : ℝ)..1,
    layerKernel N alpha * (familyCount q alpha y : ℝ)) -
    lambdaCountSegment N q y 0.36 0.478

theorem unpaidAlpha_eq_original_ranges {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    unpaidAlpha N q y =
      (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      lambdaCountSegment N q y 0 0.36 := by
  have h0 := lambdaCountIntegrand_integrable hN hy (a := 0) (b := 0.36)
    le_rfl (by norm_num) (by norm_num)
  have h1 := lambdaCountIntegrand_integrable hN hy (a := 0.36) (b := 0.478)
    (by norm_num) (by norm_num) le_rfl
  have he := intervalIntegral.integral_add_adjacent_intervals h0 h1
  unfold unpaidAlpha
  rw [original_alpha_split hN hy]
  change _ + sourceL N / Real.log ((q : ℝ) * y) *
    (∫ lam in (0 : ℝ)..(0.478 : ℝ), lambdaCountIntegrand N q y lam) - _ = _
  rw [← he]
  unfold lambdaCountSegment
  ring

theorem unpaidAlpha_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    0 ≤ unpaidAlpha N q y := by
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 ≤ Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  rw [unpaidAlpha_eq_original_ranges hN hy]
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg_of_forall (original_alpha_cutoff_mem hN hy).1
    intro alpha
    unfold layerKernel
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL)
      (Nat.cast_nonneg _)
  · unfold lambdaCountSegment
    apply mul_nonneg (div_nonneg hL hs)
    apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 0.36)
    intro lam
    unfold lambdaCountIntegrand
    positivity

theorem original_alpha_height_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha y : ℝ))
      volume (omegaCutoff N q) (sourceT N) := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have h := family_rectangle_integrable (q := q)
    (Parameters.nat_pos_of_exp_le hN) hu huT
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hi := h.integral_prod_right
  rw [intervalIntegrable_iff]
  simpa only [IntegrableOn, Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
    mul_assoc, mul_left_comm (layerKernel N _) (heightKernel _),
    integral_const_mul] using hi

theorem unpaidHeight_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y * unpaidAlpha N q y)
      volume (omegaCutoff N q) (sourceT N) := by
  simpa only [unpaidAlpha, mul_sub] using
    (original_alpha_height_integrable hN hq).sub (actual_source31_height_integrable hN hq)

theorem original_height_eq_unpaid_add_table {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha y : ℝ)) =
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y * unpaidAlpha N q y) +
      ∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * lambdaCountSegment N q y 0.36 0.478 := by
  simp only [unpaidAlpha, mul_sub]
  rw [intervalIntegral.integral_sub (original_alpha_height_integrable hN hq)
    (actual_source31_height_integrable hN hq)]
  ring

theorem highSum_le_unpaid_add_source31 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ Real.exp (-75) * q / sourceL N ^ (4 : ℕ) +
      ((∫ alpha in (19 / 20 : ℝ)..1,
        layerKernel N alpha * (familyCount q alpha (sourceT N) : ℝ)) / sourceT N +
      (∫ y in omegaCutoff N q..sourceT N, heightKernel y * unpaidAlpha N q y) +
      (q : ℝ) / sourceL N ^ (4 : ℕ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
          sourceL N ^ (4 : ℕ) * Real.exp (-s) * source31Profile (sourceL N) s) := by
  have h := original_highSum_le_density_integrals hN hq
  rw [original_height_eq_unpaid_add_table hN hq] at h
  linarith [actual_source31 hN hq]

end LiuWang.Proof.SourceRoute.HighSum.Continuation
