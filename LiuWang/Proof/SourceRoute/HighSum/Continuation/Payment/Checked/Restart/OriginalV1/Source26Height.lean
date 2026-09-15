import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.EndpointComparison
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.SmallHeightIntegral

/-! LW (2.24)--(2.26): the original logarithmic height substitution. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1

theorem height_log_substitution {q u v : ℝ} (hq : 0 < q) (hu : 0 < u)
    (huv : u ≤ v) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (Real.log (q * u)) (Real.log (q * v)))) :
    (∫ y in u..v, heightKernel y * f (Real.log (q * y))) =
      q * ∫ s in Real.log (q * u)..Real.log (q * v), Real.exp (-s) * f s := by
  have hy0 (y : ℝ) (hy : y ∈ Set.uIcc u v) : 0 < y := by
    rw [Set.uIcc_of_le huv] at hy
    exact hu.trans_le hy.1
  have hm (y : ℝ) (hy : y ∈ Set.uIcc u v) :
      Real.log (q * y) ∈ Set.Icc (Real.log (q * u)) (Real.log (q * v)) := by
    have hp := hy0 y hy
    rw [Set.uIcc_of_le huv] at hy
    exact ⟨Real.log_le_log (mul_pos hq hu) (mul_le_mul_of_nonneg_left hy.1 hq.le),
      Real.log_le_log (mul_pos hq hp) (mul_le_mul_of_nonneg_left hy.2 hq.le)⟩
  have hd (y : ℝ) (hy : y ∈ Set.uIcc u v) :
      HasDerivAt (fun y => Real.log (q * y)) (1 / y) y := by
    have h := ((hasDerivAt_id y).const_mul q).log (mul_pos hq (hy0 y hy)).ne'
    simp only [id_eq, mul_one] at h
    convert h using 1
    field_simp
  have hg : ContinuousOn (fun s => Real.exp (-s) * f s)
      ((fun y => Real.log (q * y)) '' Set.uIcc u v) := by
    apply ((Real.continuous_exp.comp continuous_neg).continuousOn.mul hf).mono
    rintro s ⟨y, hy, rfl⟩
    exact hm y hy
  have hi := intervalIntegral.integral_comp_mul_deriv' hd
    (continuousOn_const.div continuousOn_id (fun y hy => (hy0 y hy).ne')) hg
  rw [← hi, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only [Function.comp_def]
  rw [Real.exp_neg, Real.exp_log (mul_pos hq (hy0 y hy))]
  unfold heightKernel
  field_simp

theorem source26_envelope_continuousOn (L : ℝ) :
    ContinuousOn (source26AlphaEnvelope L) (Set.Ioo 0 (L / 4)) := by
  have hs (s : ℝ) (hs : s ∈ Set.Ioo 0 (L / 4)) : s ≠ 0 := ne_of_gt hs.1
  have hd (s : ℝ) (hs : s ∈ Set.Ioo 0 (L / 4)) : L - 4 * s ≠ 0 := by
    linarith [hs.2]
  unfold source26AlphaEnvelope
  fun_prop

theorem source26_envelope_nonneg {L s : ℝ}
    (hL : 0 ≤ L) (hs : 0 < s) (hd : 0 ≤ L - 4 * s) :
    0 ≤ source26AlphaEnvelope L s := by
  unfold source26AlphaEnvelope
  positivity

theorem source26_log_integrable {L a b : ℝ} (hL : 3100 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 18 * Real.log L) :
    IntervalIntegrable (fun s => Real.exp (-s) * source26AlphaEnvelope L s)
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ((Real.continuous_exp.comp continuous_neg).continuousOn.mul
    (source26_envelope_continuousOn L)).mono
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  exact ⟨ha.trans_le hs.1, by linarith [source26_denominator hL (hs.2.trans hb)]⟩

theorem source26_height_continuousOn {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    ContinuousOn (fun y => heightKernel y *
      source26AlphaEnvelope (sourceL N) (Real.log ((q : ℝ) * y)))
      (Set.Icc (omegaCutoff N q) (sourceT N)) := by
  have hy0 (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) : 0 < y := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq, hy.1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqy (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (sourceT N)) :
      (q : ℝ) * y ≠ 0 := (mul_pos hq0 (hy0 y hy)).ne'
  have hlog : ContinuousOn (fun y => Real.log ((q : ℝ) * y))
      (Set.Icc (omegaCutoff N q) (sourceT N)) := by fun_prop
  apply ContinuousOn.mul
  · unfold heightKernel
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (hy0 y hy).ne')
  · apply (source26_envelope_continuousOn (sourceL N)).comp hlog
    intro y hy
    refine ⟨by linarith [original_log_product_ge_ten hN hy.1], ?_⟩
    linarith [source26_denominator (Parameters.sourceL_ge_3100 hN)
      (original_log_product_upper hN hq (hy0 y hy) hy.2)]

theorem source26_envelope_log_height {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {v : ℝ} (huv : omegaCutoff N q ≤ v) (hvT : v ≤ sourceT N) :
    (∫ y in v..sourceT N, heightKernel y *
      source26AlphaEnvelope (sourceL N) (Real.log ((q : ℝ) * y))) ≤
      (q : ℝ) / sourceL N ^ (4 : ℕ) *
        ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
          Real.exp (-s) *
            ((17102 + 254231 / s) * s ^ (6 : ℕ) * sourceL N ^ (5 : ℕ) /
                (sourceL N - 4 * s) * Real.exp (-0.478 * (sourceL N - 4 * s) / s) +
              16541 * s ^ (6 : ℕ) * sourceL N ^ (4 : ℕ) *
                Real.exp (-0.478 * sourceL N / s)) := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hu0 : 0 < omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hv0 := hu0.trans_le huv
  have hb := original_log_height_bounds hN hq
  have hAv : Real.log (3.36 * sourceP N) ≤ Real.log ((q : ℝ) * v) := by
    rw [← hb.1]
    exact Real.log_le_log (mul_pos hq0 hu0) (mul_le_mul_of_nonneg_left huv hq0.le)
  have hvlog : Real.log ((q : ℝ) * v) ≤ Real.log ((q : ℝ) * sourceT N) :=
    Real.log_le_log (mul_pos hq0 hv0) (mul_le_mul_of_nonneg_left hvT hq0.le)
  have hB : Real.log (sourceP N * sourceT N) = 18 * Real.log (sourceL N) := by
    rw [sourceP, sourceT, Real.log_mul (pow_pos hL0 _).ne' (pow_pos hL0 _).ne',
      Real.log_pow, Real.log_pow]
    norm_num
    ring
  have hc : ContinuousOn (source26AlphaEnvelope (sourceL N))
      (Set.Icc (Real.log ((q : ℝ) * v)) (Real.log ((q : ℝ) * sourceT N))) := by
    apply (source26_envelope_continuousOn (sourceL N)).mono
    intro s hs
    refine ⟨hb.2.1.trans_le (hAv.trans hs.1), ?_⟩
    have hsB := hs.2.trans hb.2.2.2
    rw [hB] at hsB
    linarith [source26_denominator hL hsB]
  have hi := source26_log_integrable hL hb.2.1 (hb.2.2.1.trans hb.2.2.2) hB.le
  have he :
      (q : ℝ) / sourceL N ^ (4 : ℕ) *
        (∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
          sourceL N ^ (4 : ℕ) * Real.exp (-s) * source26AlphaEnvelope (sourceL N) s) =
      (q : ℝ) * ∫ s in Real.log (3.36 * sourceP N)..Real.log (sourceP N * sourceT N),
        Real.exp (-s) * source26AlphaEnvelope (sourceL N) s := by
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    field_simp
  simp_rw [← source26_normalization]
  rw [he, height_log_substitution hq0 hv0 hvT hc]
  apply mul_le_mul_of_nonneg_left _ hq0.le
  apply intervalIntegral.integral_mono_interval hAv hvlog hb.2.2.2 _ hi
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro s hs
  have hsB : s ≤ 18 * Real.log (sourceL N) := hs.2.trans hB.le
  exact mul_nonneg (Real.exp_pos _).le
    (source26_envelope_nonneg hL0.le (hb.2.1.trans hs.1)
      (source26_denominator hL hsB).le)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1
