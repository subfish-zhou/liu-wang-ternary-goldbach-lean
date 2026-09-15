import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Slices

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

def bandWindow (q : ℕ) (a b : ℝ) : Set (ℝ × ℝ) :=
  {z | 1 - b / Real.log ((q : ℝ) * z.2) < z.1 ∧
    z.1 ≤ 1 - a / Real.log ((q : ℝ) * z.2)}

theorem bandWindow_measurable (q : ℕ) (a b : ℝ) : MeasurableSet (bandWindow q a b) := by
  have hl : Measurable (fun z : ℝ × ℝ => 1 - b / Real.log ((q : ℝ) * z.2)) := by fun_prop
  have hu : Measurable (fun z : ℝ × ℝ => 1 - a / Real.log ((q : ℝ) * z.2)) := by fun_prop
  exact (measurableSet_lt hl measurable_fst).inter (measurableSet_le measurable_fst hu)

theorem bandWindow_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a b : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478) :
    (∫ alpha in (19 / 20 : ℝ)..1, (bandWindow q a b).indicator
      (fun z : ℝ × ℝ => layerKernel N z.1 * heightKernel z.2 *
        (familyCount q z.1 z.2 : ℝ)) (alpha, y)) =
      heightKernel y * lambdaCountSegment N q y a b := by
  have hs : 0 < Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy]
  have h1 : (19 / 20 : ℝ) ≤ 1 - b / Real.log ((q : ℝ) * y) :=
    (original_alpha_cutoff_mem hN hy).1.trans
      (sub_le_sub_left (div_le_div_of_nonneg_right hb hs.le) 1)
  have h2 : 1 - b / Real.log ((q : ℝ) * y) ≤ 1 - a / Real.log ((q : ℝ) * y) :=
    sub_le_sub_left (div_le_div_of_nonneg_right hab hs.le) 1
  have h3 : 1 - a / Real.log ((q : ℝ) * y) ≤ 1 := by
    linarith [div_nonneg ha hs.le]
  have he (alpha : ℝ) :
      (bandWindow q a b).indicator
        (fun z : ℝ × ℝ => layerKernel N z.1 * heightKernel z.2 *
          (familyCount q z.1 z.2 : ℝ)) (alpha, y) =
      (Set.Ioc (1 - b / Real.log ((q : ℝ) * y))
        (1 - a / Real.log ((q : ℝ) * y))).indicator
          (fun alpha => layerKernel N alpha * heightKernel y *
            (familyCount q alpha y : ℝ)) alpha := by
    simp only [Set.indicator_apply, bandWindow, Set.mem_ofPred_eq, Set.mem_Ioc]
  simp_rw [he]
  rw [integral_Ioc_indicator _ h1 h2 h3]
  simp_rw [mul_assoc, mul_left_comm (layerKernel N _) (heightKernel y)]
  rw [intervalIntegral.integral_const_mul, actual_lambda_substitution]
  rfl

theorem band_height_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478) :
    IntervalIntegrable (fun y => heightKernel y * lambdaCountSegment N q y a b)
      volume (omegaCutoff N q) (sourceT N) := by
  have hu : 0 < omegaCutoff N q := by linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have h := (family_rectangle_integrable (q := q)
    (Parameters.nat_pos_of_exp_le hN) hu huT).indicator (bandWindow_measurable q a b)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hi := h.integral_prod_right
  rw [intervalIntegrable_iff]
  apply hi.congr
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huT] at hy
  simpa only [Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] using
    bandWindow_slice hN hy.1.le ha hab hb

def finiteK3 (N q : ℕ) [NeZero q] : ℝ :=
  ∫ y in omegaCutoff N q..sourceT N,
    heightKernel y * lambdaCountSegment N q y (1 / c1) 0.36

def zeroTail (N q : ℕ) [NeZero q] : ℝ :=
  ∫ y in omegaCutoff N q..sourceT N,
    heightKernel y * lambdaCountSegment N q y 0 (1 / c1)

def heightEnvelope (f : ℝ → ℝ → ℝ) (N q : ℕ) : ℝ :=
  ∫ y in omegaCutoff N q..sourceT N, heightKernel y * f (sourceL N) (Real.log ((q : ℝ) * y))

theorem original_height_zero_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N, heightKernel y * lambdaCountSegment N q y 0 0.36) =
      zeroTail N q + finiteK3 N q := by
  have he : (∫ y in omegaCutoff N q..sourceT N, heightKernel y * lambdaCountSegment N q y 0 0.36) =
      ∫ y in omegaCutoff N q..sourceT N,
        heightKernel y * lambdaCountSegment N q y 0 (1 / c1) +
          heightKernel y * lambdaCountSegment N q y (1 / c1) 0.36 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)] at hy
    dsimp only
    rw [original_zero_tail_split hN hy.1, mul_add]
  rw [he, intervalIntegral.integral_add
    (band_height_integrable hN hq le_rfl c1_bounds.1.le (by linarith [c1_bounds.2.1]))
    (band_height_integrable hN hq c1_bounds.1.le (by linarith [c1_bounds.2.1]) (by norm_num))]
  rfl

theorem log_integrable {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => Real.exp (-s) * f s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ((Real.continuous_exp.comp continuous_neg).continuousOn.mul hf).mono
  rw [Set.uIcc_of_le hab]
  exact fun _ hs => ha.trans_le hs.1

theorem log_substitution {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {q u T : ℝ} (hq : 0 < q) (hu : 0 < u) (huT : u ≤ T) (hqu : 1 < q * u) :
    (∫ y in u..T, heightKernel y * f (Real.log (q * y))) =
      q * ∫ s in Real.log (q * u)..Real.log (q * T), Real.exp (-s) * f s := by
  have hy0 (y : ℝ) (hy : y ∈ Set.uIcc u T) : 0 < y := by
    rw [Set.uIcc_of_le huT] at hy
    exact hu.trans_le hy.1
  have hd (y : ℝ) (hy : y ∈ Set.uIcc u T) :
      HasDerivAt (fun y => Real.log (q * y)) (1 / y) y := by
    have hh := ((hasDerivAt_id y).const_mul q).log (mul_pos hq (hy0 y hy)).ne'
    simp only [id_eq, mul_one] at hh
    convert hh using 1
    field_simp
  have hg : ContinuousOn (fun s => Real.exp (-s) * f s)
      ((fun y => Real.log (q * y)) '' Set.uIcc u T) := by
    apply ((Real.continuous_exp.comp continuous_neg).continuousOn.mul hf).mono
    rintro s ⟨y, hy, rfl⟩
    rw [Set.uIcc_of_le huT] at hy
    exact Real.log_pos (hqu.trans_le (mul_le_mul_of_nonneg_left hy.1 hq.le))
  have hi := intervalIntegral.integral_comp_mul_deriv' hd
    (continuousOn_const.div continuousOn_id (fun y hy => (hy0 y hy).ne')) hg
  rw [← hi, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' := hy0 y hy
  dsimp only [Function.comp_def]
  rw [Real.exp_neg, Real.exp_log (mul_pos hq hy')]
  unfold heightKernel
  field_simp

theorem envelope_integrable {f : ℝ → ℝ → ℝ} (hf : ∀ L, ContinuousOn (f L) (Set.Ioi 0))
    {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y * f (sourceL N) (Real.log ((q : ℝ) * y)))
      volume (omegaCutoff N q) (sourceT N) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (WeightedLowZeros.omegaCutoff_le_sourceT hN)]
  have hy0 (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) : 0 < y := by
    linarith [(original_table_domain hN hq hy.1).1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlog := (continuousOn_const.mul continuousOn_id).log
    (fun y hy => (mul_pos hq0 (hy0 y hy)).ne')
  exact (continuousOn_const.div (continuousOn_id.pow 2)
    (fun y hy => (pow_pos (hy0 y hy) 2).ne')).mul
      ((hf _).comp hlog (fun y hy => by
        change 0 < Real.log ((q : ℝ) * y)
        linarith [original_log_product_ge_ten hN hy.1]))

theorem envelope_log_exact {f : ℝ → ℝ → ℝ} (hf : ∀ L, ContinuousOn (f L) (Set.Ioi 0))
    {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    heightEnvelope f N q = (q : ℝ) / sourceL N ^ 4 *
      ∫ s in lower (sourceL N)..Real.log ((q : ℝ) * sourceT N), integrand f (sourceL N) s := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hu0 := Parameters.omegaCutoff_pos (Parameters.exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  have hp := original_product_ge hN (q := q) le_rfl
  have hL : sourceL N ≠ 0 := by linarith [Parameters.sourceL_ge_3100 hN]
  rw [heightEnvelope, log_substitution (hf _) hq0 hu0
    (WeightedLowZeros.omegaCutoff_le_sourceT hN) (by linarith),
    (original_log_height_bounds hN hq).1]
  unfold integrand
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  change _ = (q : ℝ) / sourceL N ^ 4 * (sourceL N ^ 4 * _)
  field_simp
  rfl

theorem envelope_log_extension {f : ℝ → ℝ → ℝ}
    (hf : ∀ L, ContinuousOn (f L) (Set.Ioi 0))
    (hpos : ∀ L s, 0 < L → 0 < s → 0 ≤ f L s)
    {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    heightEnvelope f N q ≤ (q : ℝ) / sourceL N ^ 4 *
      ∫ s in lower (sourceL N)..upper (sourceL N), integrand f (sourceL N) s := by
  rw [envelope_log_exact hf hN hq]
  have hb := original_log_height_bounds hN hq
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_interval le_rfl hb.2.2.1 hb.2.2.2
  · apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro s hs
    exact mul_nonneg (by positivity) (hpos _ _ hL (hb.2.1.trans hs.1))
  · unfold integrand
    simpa only [mul_assoc] using
      (log_integrable (hf _) hb.2.1 (hb.2.2.1.trans hb.2.2.2)).const_mul (sourceL N ^ 4)

theorem actual_source35_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), FirstCase q y) :
    finiteK3 N q ≤ heightEnvelope profile35 N q := by
  apply intervalIntegral.integral_mono_on (WeightedLowZeros.omegaCutoff_le_sourceT hN)
    (band_height_integrable hN hq c1_bounds.1.le (by linarith [c1_bounds.2.1]) (by norm_num))
    (envelope_integrable profile35_continuousOn hN hq)
  intro y hy
  exact mul_le_mul_of_nonneg_left (actual_source35_slice hN hq hy.1 (hcase y hy))
    (by unfold heightKernel; positivity)

theorem actual_source36_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    finiteK3 N q ≤ heightEnvelope profile36 N q := by
  apply intervalIntegral.integral_mono_on (WeightedLowZeros.omegaCutoff_le_sourceT hN)
    (band_height_integrable hN hq c1_bounds.1.le (by linarith [c1_bounds.2.1]) (by norm_num))
    (envelope_integrable profile36_continuousOn hN hq)
  intro y hy
  exact mul_le_mul_of_nonneg_left (actual_source36_slice hN hq hy.1 (hcase y hy))
    (by unfold heightKernel; positivity)

theorem actual_source35_scalar {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), FirstCase q y) :
    finiteK3 N q ≤ (q : ℝ) / sourceL N ^ 4 * scalar35 (sourceL N) :=
  (actual_source35_height hN hq hcase).trans
    (envelope_log_extension profile35_continuousOn (fun _ _ => profile35_nonneg) hN hq)

theorem actual_source36_scalar {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hcase : ∀ y ∈ Set.Icc (omegaCutoff N q) (sourceT N), SecondCase q y) :
    finiteK3 N q ≤ (q : ℝ) / sourceL N ^ 4 * scalar36 (sourceL N) :=
  (actual_source36_height hN hq hcase).trans
    (envelope_log_extension profile36_continuousOn (fun _ _ => profile36_nonneg) hN hq)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
