import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.SmallHeight

/-! # Integrability and actual outer-height consumption of (2.25) -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart

theorem smallAlpha_window_measurable (q : ℕ) :
    MeasurableSet {z : ℝ × ℝ |
      (19 / 20 : ℝ) < z.1 ∧ z.1 ≤ 1 - 0.478 / Real.log ((q : ℝ) * z.2)} := by
  have hu : Measurable (fun z : ℝ × ℝ => 1 - 0.478 / Real.log ((q : ℝ) * z.2)) := by
    fun_prop
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst hu)

theorem actual_smallAlpha_height_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ))
      volume (omegaCutoff N q) (sourceT N) := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have h := (family_rectangle_integrable (q := q)
    (Parameters.nat_pos_of_exp_le hN) hu huT).indicator (smallAlpha_window_measurable q)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hi := h.integral_prod_right
  rw [intervalIntegrable_iff]
  apply hi.congr
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huT] at hy
  have hb := original_alpha_cutoff_mem hN hy.1.le
  have he :
      (∫ alpha in (19 / 20 : ℝ)..1,
        ({z : ℝ × ℝ | (19 / 20 : ℝ) < z.1 ∧
          z.1 ≤ 1 - 0.478 / Real.log ((q : ℝ) * z.2)}).indicator
            (fun z => layerKernel N z.1 * heightKernel z.2 *
              (familyCount q z.1 z.2 : ℝ)) (alpha, y)) =
        heightKernel y * ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
          layerKernel N alpha * (familyCount q alpha y : ℝ) := by
    have hf (alpha : ℝ) :
        ({z : ℝ × ℝ | (19 / 20 : ℝ) < z.1 ∧
          z.1 ≤ 1 - 0.478 / Real.log ((q : ℝ) * z.2)}).indicator
            (fun z => layerKernel N z.1 * heightKernel z.2 *
              (familyCount q z.1 z.2 : ℝ)) (alpha, y) =
        (Set.Ioc (19 / 20 : ℝ) (1 - 0.478 / Real.log ((q : ℝ) * y))).indicator
          (fun alpha => layerKernel N alpha * heightKernel y *
            (familyCount q alpha y : ℝ)) alpha := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc]
    simp_rw [hf]
    rw [integral_Ioc_indicator _ le_rfl hb.1 hb.2]
    simp_rw [mul_assoc, mul_left_comm (layerKernel N _) (heightKernel y)]
    rw [intervalIntegral.integral_const_mul]
  simpa only [Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] using he

theorem source25_height_continuousOn {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ContinuousOn (fun y => heightKernel y * ((q.totient : ℝ) * source25Bound q y) *
      (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
        Real.exp (-sourceL N / 20))) (Set.Icc (omegaCutoff N q) (sourceT N)) := by
  have hy0 (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) : y ≠ 0 := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq, hy.1]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hs (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) :
      Real.log ((q : ℝ) * y) ≠ 0 := by
    linarith [original_log_product_ge_ten hN hy.1]
  have hy2 (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) :
      y ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ (hy0 y hy)
  have hqy (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) :
      (q : ℝ) * y ≠ 0 := mul_ne_zero hq0 (hy0 y hy)
  unfold heightKernel source25Bound
  fun_prop

theorem actual_source25_outer_signed {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N) :
    (∫ y in omegaCutoff N q..v, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      ∫ y in omegaCutoff N q..v,
        heightKernel y * ((q.totient : ℝ) * source25Bound q y) *
          (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
            Real.exp (-sourceL N / 20)) := by
  have hsub : Set.uIcc (omegaCutoff N q) v ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc le_rfl hvT
  have hm := ((source25_height_continuousOn hN hq).intervalIntegrable_of_Icc (μ := volume)
    (huv.trans hvT)).mono_set hsub
  apply intervalIntegral.integral_mono_on huv
    ((actual_smallAlpha_height_integrable hN hq).mono_set hsub) hm
  intro y hy
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (actual_source25_alpha_signed hN hq hy.1) (by unfold heightKernel; positivity)

theorem lowLambda_height_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y * lambdaCountSegment N q y 0 0.36)
      volume (omegaCutoff N q) (sourceT N) := by
  apply ((unpaidHeight_integrable hN hq).sub
    (actual_smallAlpha_height_integrable hN hq)).congr
  intro y hy
  rw [Set.uIoc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)] at hy
  dsimp only
  rw [unpaidAlpha_eq_original_ranges hN hy.1.le]
  ring

theorem actual_unpaid_small_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N) :
    (∫ y in omegaCutoff N q..v, heightKernel y * unpaidAlpha N q y) ≤
      (∫ y in omegaCutoff N q..v,
        heightKernel y * ((q.totient : ℝ) * source25Bound q y) *
          (Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) -
            Real.exp (-sourceL N / 20))) +
      ∫ y in omegaCutoff N q..v, heightKernel y * lambdaCountSegment N q y 0 0.36 := by
  have hsub : Set.uIcc (omegaCutoff N q) v ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc le_rfl hvT
  have he :
      (∫ y in omegaCutoff N q..v, heightKernel y * unpaidAlpha N q y) =
      (∫ y in omegaCutoff N q..v, heightKernel y *
        ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
          layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      ∫ y in omegaCutoff N q..v, heightKernel y * lambdaCountSegment N q y 0 0.36 := by
    rw [← intervalIntegral.integral_add
      ((actual_smallAlpha_height_integrable hN hq).mono_set hsub)
      ((lowLambda_height_integrable hN hq).mono_set hsub)]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le huv] at hy
    dsimp only
    rw [unpaidAlpha_eq_original_ranges hN hy.1]
    ring
  rw [he]
  linarith [actual_source25_outer_signed hN hq huv hvT]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart
