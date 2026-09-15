import LiuWang.Proof.SourceRoute.HighSum.Continuation.TableIntegral
import LiuWang.Proof.SourceRoute.HighSum.SourceReduction

/-! # Full original height integral of the paid table contribution -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation

def source31Window (q : ℕ) : Set (ℝ × ℝ) :=
  {z | 1 - 0.478 / Real.log ((q : ℝ) * z.2) < z.1 ∧
    z.1 ≤ 1 - 0.36 / Real.log ((q : ℝ) * z.2)}

theorem source31Window_measurable (q : ℕ) : MeasurableSet (source31Window q) := by
  have hl : Measurable (fun z : ℝ × ℝ => 1 - 0.478 / Real.log ((q : ℝ) * z.2)) := by
    fun_prop
  have hu : Measurable (fun z : ℝ × ℝ => 1 - 0.36 / Real.log ((q : ℝ) * z.2)) := by
    fun_prop
  exact (measurableSet_lt hl measurable_fst).inter (measurableSet_le measurable_fst hu)

theorem original_source31_endpoints {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (19 / 20 : ℝ) ≤ 1 - 0.478 / Real.log ((q : ℝ) * y) ∧
    1 - 0.478 / Real.log ((q : ℝ) * y) ≤ 1 - 0.36 / Real.log ((q : ℝ) * y) ∧
    1 - 0.36 / Real.log ((q : ℝ) * y) ≤ 1 := by
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  refine ⟨(original_alpha_cutoff_mem hN hy).1, ?_, ?_⟩
  · exact sub_le_sub_left
      (div_le_div_of_nonneg_right (by norm_num : (0.36 : ℝ) ≤ 0.478) hs.le) 1
  · have : 0 ≤ (0.36 : ℝ) / Real.log ((q : ℝ) * y) := by positivity
    linarith

theorem integral_Ioc_indicator (f : ℝ → ℝ) {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (∫ x in a..b, (Set.Ioc c d).indicator f x) = ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le (hac.trans (hcd.trans hdb)),
    intervalIntegral.integral_of_le hcd, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hs : Set.Ioc c d ∩ Set.Ioc a b = Set.Ioc c d :=
    Set.inter_eq_left.mpr (Set.Ioc_subset_Ioc hac hdb)
  rw [hs]

theorem source31Window_slice {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (∫ alpha in (19 / 20 : ℝ)..1,
      (source31Window q).indicator
        (fun z : ℝ × ℝ => layerKernel N z.1 * heightKernel z.2 *
          (familyCount q z.1 z.2 : ℝ)) (alpha, y)) =
      heightKernel y * lambdaCountSegment N q y 0.36 0.478 := by
  have he := original_source31_endpoints hN hy
  have hf (alpha : ℝ) :
      (source31Window q).indicator
        (fun z : ℝ × ℝ => layerKernel N z.1 * heightKernel z.2 *
          (familyCount q z.1 z.2 : ℝ)) (alpha, y) =
      (Set.Ioc (1 - 0.478 / Real.log ((q : ℝ) * y))
        (1 - 0.36 / Real.log ((q : ℝ) * y))).indicator
          (fun alpha => layerKernel N alpha * heightKernel y *
            (familyCount q alpha y : ℝ)) alpha := by
    simp only [Set.indicator_apply, source31Window, Set.mem_ofPred_eq,
      Set.mem_Ioc]
  simp_rw [hf]
  rw [integral_Ioc_indicator _ he.1 he.2.1 he.2.2]
  simp_rw [mul_assoc, mul_left_comm (layerKernel N _) (heightKernel y)]
  rw [intervalIntegral.integral_const_mul, actual_lambda_substitution]
  rfl

theorem actual_source31_height_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y =>
      heightKernel y * lambdaCountSegment N q y 0.36 0.478)
      volume (omegaCutoff N q) (sourceT N) := by
  have hu : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have h := (family_rectangle_integrable (q := q)
    (Parameters.nat_pos_of_exp_le hN) hu huT).indicator (source31Window_measurable q)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hi := h.integral_prod_right
  rw [intervalIntegrable_iff]
  apply hi.congr
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro y hy
  rw [Set.uIoc_of_le huT] at hy
  simpa only [Set.uIoc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] using
    source31Window_slice hN hy.1.le

theorem source31Profile_continuousOn (L : ℝ) :
    ContinuousOn (source31Profile L) (Set.Ioi 0) := by
  have hs : ∀ x ∈ Set.Ioi (0 : ℝ), x ≠ 0 := fun x hx => ne_of_gt hx
  unfold source31Profile
  fun_prop

theorem source31_height_majorant_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y *
      source31Profile (sourceL N) (Real.log ((q : ℝ) * y)))
      volume (omegaCutoff N q) (sourceT N) := by
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huT]
  have hy0 (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) : 0 < y := by
    linarith [(original_table_domain hN hq hy.1).1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlog : ContinuousOn (fun y => Real.log ((q : ℝ) * y))
      (Set.Icc (omegaCutoff N q) (sourceT N)) :=
    (continuousOn_const.mul continuousOn_id).log (fun y hy => (mul_pos hq0 (hy0 y hy)).ne')
  exact (continuousOn_const.div (continuousOn_id.pow 2)
    (fun y hy => (pow_pos (hy0 y hy) 2).ne')).mul
      ((source31Profile_continuousOn _).comp hlog (fun y hy => by
        have := original_log_product_ge_ten hN hy.1
        change 0 < Real.log ((q : ℝ) * y)
        linarith))

theorem actual_source31_full_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0.36 0.478) ≤
    ∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * source31Profile (sourceL N) (Real.log ((q : ℝ) * y)) := by
  apply intervalIntegral.integral_mono_on (WeightedLowZeros.omegaCutoff_le_sourceT hN)
    (actual_source31_height_integrable hN hq) (source31_height_majorant_integrable hN hq)
  intro y hy
  exact mul_le_mul_of_nonneg_left (actual_source31_slice hN hq hy.1) (by
    unfold heightKernel
    positivity)

end LiuWang.Proof.SourceRoute.HighSum.Continuation
