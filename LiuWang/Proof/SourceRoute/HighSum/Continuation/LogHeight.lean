import LiuWang.Proof.SourceRoute.HighSum.Continuation.TableHeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The exact logarithmic height substitution in source (2.31) -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation

theorem source31Profile_nonneg {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    0 ≤ source31Profile L s := by
  have h (a b : ℝ) (hab : a ≤ b) : 0 ≤ lambdaSegment L s a b := by
    unfold lambdaSegment
    exact mul_nonneg (div_nonneg hL.le hs.le)
      (intervalIntegral.integral_nonneg_of_forall hab (fun _ => (Real.exp_pos _).le))
  rw [source31Profile, ← source31_signed_segments hL hs]
  have h1 := h 0.36 0.39 (by norm_num)
  have h2 := h 0.39 0.42 (by norm_num)
  have h3 := h 0.42 0.45 (by norm_num)
  have h4 := h 0.45 0.46 (by norm_num)
  have h5 := h 0.46 0.47 (by norm_num)
  have h6 := h 0.47 0.475 (by norm_num)
  have h7 := h 0.475 0.478 (by norm_num)
  positivity

theorem source31_log_integrand_continuousOn (L : ℝ) :
    ContinuousOn (fun s => Real.exp (-s) * source31Profile L s) (Set.Ioi 0) :=
  Real.continuous_exp.comp continuous_neg |>.continuousOn |>.mul
    (source31Profile_continuousOn L)

theorem source31_log_integrand_integrable (L : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => Real.exp (-s) * source31Profile L s) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (source31_log_integrand_continuousOn L).mono
  rw [Set.uIcc_of_le hab]
  exact fun s hs => ha.trans_le hs.1

theorem source31_log_substitution (L : ℝ) {q u T : ℝ}
    (hq : 0 < q) (hu : 0 < u) (huT : u ≤ T) (hqu : 1 < q * u) :
    (∫ y in u..T, heightKernel y * source31Profile L (Real.log (q * y))) =
      q * ∫ s in Real.log (q * u)..Real.log (q * T),
        Real.exp (-s) * source31Profile L s := by
  have hy0 (y : ℝ) (hy : y ∈ Set.uIcc u T) : 0 < y := by
    rw [Set.uIcc_of_le huT] at hy
    exact hu.trans_le hy.1
  have hd (y : ℝ) (hy : y ∈ Set.uIcc u T) :
      HasDerivAt (fun y => Real.log (q * y)) (1 / y) y := by
    have hh := ((hasDerivAt_id y).const_mul q).log (mul_pos hq (hy0 y hy)).ne'
    simp only [id_eq, mul_one] at hh
    have he : q / (q * y) = 1 / y := by field_simp
    rw [he] at hh
    exact hh
  have hg : ContinuousOn (fun s => Real.exp (-s) * source31Profile L s)
      ((fun y => Real.log (q * y)) '' Set.uIcc u T) := by
    apply (source31_log_integrand_continuousOn L).mono
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

theorem original_log_height_bounds {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Real.log ((q : ℝ) * omegaCutoff N q) = Real.log (3.36 * sourceP N) ∧
      0 < Real.log (3.36 * sourceP N) ∧
      Real.log (3.36 * sourceP N) ≤ Real.log ((q : ℝ) * sourceT N) ∧
      Real.log ((q : ℝ) * sourceT N) ≤ Real.log (sourceP N * sourceT N) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hu0 := Parameters.omegaCutoff_pos
    (Parameters.exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  have ht0 := Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN)
  have he : (q : ℝ) * omegaCutoff N q = 3.36 * sourceP N := by
    unfold omegaCutoff
    field_simp
  have hl : 0 < Real.log ((q : ℝ) * omegaCutoff N q) := by
    linarith [original_log_product_ge_ten hN (q := q) le_rfl]
  refine ⟨congrArg Real.log he, by simpa only [he] using hl, ?_, ?_⟩
  · rw [← he]
    exact Real.log_le_log (mul_pos hq0 hu0)
      (mul_le_mul_of_nonneg_left (WeightedLowZeros.omegaCutoff_le_sourceT hN) hq0.le)
  · exact Real.log_le_log (mul_pos hq0 ht0) (mul_le_mul_of_nonneg_right hq ht0.le)

theorem actual_source31_log_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0.36 0.478) ≤
      (q : ℝ) * ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
        Real.exp (-s) * source31Profile (sourceL N) s := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hu0 := Parameters.omegaCutoff_pos
    (Parameters.exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have hp := original_product_ge hN (q := q) le_rfl
  have hb := original_log_height_bounds hN hq
  have hL : 0 < sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  calc
    _ ≤ _ := actual_source31_full_height hN hq
    _ = (q : ℝ) * ∫ s in Real.log (3.36 * sourceP N)..Real.log ((q : ℝ) * sourceT N),
        Real.exp (-s) * source31Profile (sourceL N) s := by
      rw [source31_log_substitution _ hq0 hu0 huT (by linarith), hb.1]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hq0.le
      apply intervalIntegral.integral_mono_interval le_rfl hb.2.2.1 hb.2.2.2
        _ (source31_log_integrand_integrable _ hb.2.1 (hb.2.2.1.trans hb.2.2.2))
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro s hs
      exact mul_nonneg (Real.exp_pos _).le (source31Profile_nonneg hL (hb.2.1.trans hs.1))

theorem actual_source31 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in omegaCutoff N q..sourceT N,
      heightKernel y * lambdaCountSegment N q y 0.36 0.478) ≤
      (q : ℝ) / sourceL N ^ (4 : ℕ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
          sourceL N ^ (4 : ℕ) * Real.exp (-s) * source31Profile (sourceL N) s := by
  have hL : sourceL N ≠ 0 := by linarith [Parameters.sourceL_ge_3100 hN]
  have he : (q : ℝ) / sourceL N ^ (4 : ℕ) *
      (∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
        sourceL N ^ (4 : ℕ) * Real.exp (-s) * source31Profile (sourceL N) s) =
      (q : ℝ) * ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
        Real.exp (-s) * source31Profile (sourceL N) s := by
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    field_simp
  rw [he]
  exact actual_source31_log_height hN hq

end LiuWang.Proof.SourceRoute.HighSum.Continuation
