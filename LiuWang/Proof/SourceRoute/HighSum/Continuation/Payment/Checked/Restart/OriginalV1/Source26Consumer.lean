import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source26Height

/-! The actual K2 large-height integral, conditional only on the printed T7.

The final integral is exactly (2.26); its 0.00031 numerical payment is not
assumed here. No small-height phi factor or source-check edge is consumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1

theorem source24_actual_integral_compare {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    {y : ℝ} (hy : omegaCutoff N q ≤ y)
    (hyD : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
    ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * Applications.sourceSevenBound q alpha y := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have hy0 : 0 < y := by
    have hp := original_product_ge hN hy
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    exact (mul_pos_iff_of_pos_left hq0).mp (by linarith)
  have hb := original_alpha_cutoff_mem hN hy
  have hb1 : 1 - 0.478 / Real.log ((q : ℝ) * y) < 1 := by
    have hd : 0 < (0.478 : ℝ) / Real.log ((q : ℝ) * y) := by positivity
    linarith
  have hsub : Set.uIcc (19 / 20 : ℝ) (1 - 0.478 / Real.log ((q : ℝ) * y)) ⊆
      Set.uIcc (19 / 20 : ℝ) 1 := by
    rw [Set.uIcc_of_le hb.1, Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl hb.2
  apply intervalIntegral.integral_mono_on hb.1
    ((family_alpha_integrable hn y).mono_set hsub)
    (sourceSeven_integrand_integrable hn hy0 hs _ _)
  intro alpha ha
  exact mul_le_mul_of_nonneg_left
    (hT7 alpha y (by linarith [ha.1]) (ha.2.trans_lt hb1) hyD)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL)

theorem source26_actual_alpha {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) (hyT : y ≤ sourceT N)
    (hyD : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      source26AlphaEnvelope (sourceL N) (Real.log ((q : ℝ) * y)) :=
  (source24_actual_integral_compare hN hT7 hy hyD).trans
    (source24_to_source26 hN hq hy hyT)

theorem source26_actual_large_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hT7 : ∀ (alpha y : ℝ), 1 / 2 ≤ alpha → alpha < 1 →
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y →
      (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N)
    (hvD : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ v) :
    (∫ y in v..sourceT N, heightKernel y *
      ∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ)) ≤
      (q : ℝ) / sourceL N ^ (4 : ℕ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
          Real.exp (-s) *
            ((17102 + 254231 / s) * s ^ (6 : ℕ) * sourceL N ^ (5 : ℕ) /
                (sourceL N - 4 * s) * Real.exp (-0.478 * (sourceL N - 4 * s) / s) +
              16541 * s ^ (6 : ℕ) * sourceL N ^ (4 : ℕ) *
                Real.exp (-0.478 * sourceL N / s)) := by
  have hsub : Set.uIcc v (sourceT N) ⊆
      Set.uIcc (omegaCutoff N q) (sourceT N) := by
    rw [Set.uIcc_of_le hvT, Set.uIcc_of_le (huv.trans hvT)]
    exact Set.Icc_subset_Icc huv le_rfl
  apply le_trans _ (source26_envelope_log_height hN hq huv hvT)
  apply intervalIntegral.integral_mono_on hvT
    ((actual_smallAlpha_height_integrable hN hq).mono_set hsub)
    (((source26_height_continuousOn hN hq).intervalIntegrable_of_Icc
      (μ := volume) (huv.trans hvT)).mono_set hsub)
  intro y hy
  exact mul_le_mul_of_nonneg_left
    (source26_actual_alpha hN hq hT7 (huv.trans hy.1) hy.2 (hvD.trans hy.1))
    (by unfold heightKernel; positivity)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
