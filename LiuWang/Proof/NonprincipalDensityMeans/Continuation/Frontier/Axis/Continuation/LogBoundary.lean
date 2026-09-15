import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.AxisMean
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-! Pay the actual H logarithmic vertical sides, without assuming a Littlewood counting formula. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

theorem log_H_le_square {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    Real.log ‖H chi X s‖ ≤ ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 := by
  by_cases hz : H chi X s = 0
  · simp only [hz, norm_zero, Real.log_zero]
    exact sq_nonneg _
  have hn : ‖H chi X s‖ ≤ 1 + ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 := by
    have h := norm_sub_le (1 : ℂ) (NonprincipalDensityAdvance.f chi X s ^ (2 : ℕ))
    rw [norm_one, norm_pow] at h
    exact h
  exact (Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz)).trans (by linarith)

theorem posLog_H_le_square {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    Real.posLog ‖H chi X s‖ ≤ ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 :=
  max_le (sq_nonneg _) (log_H_le_square chi X s)

theorem log_H_vertical_integrable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X sigma u : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖H chi X ((sigma : ℂ) + t * Complex.I)‖)
      volume (-u) u := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  apply AnalyticOnNhd.meromorphicOn
  intro t _
  have h := ((differentiable_H hchi X).analyticAt ((sigma : ℂ) + t * Complex.I)).restrictScalars
    (𝕜 := ℝ)
  have ha : AnalyticAt ℝ (fun r : ℝ => (sigma : ℂ) + r * Complex.I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact AnalyticAt.comp (f := fun r : ℝ => (sigma : ℂ) + r * Complex.I) h ha

theorem posLog_H_vertical_continuous {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X sigma : ℝ) :
    Continuous (fun t : ℝ => Real.posLog ‖H chi X ((sigma : ℂ) + t * Complex.I)‖) :=
  Real.continuous_posLog.comp (((differentiable_H hchi X).continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm)

theorem log_H_window_le_Fmean (q : ℕ) [NeZero q] (X sigma : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -u..u,
      Real.log ‖H chi X ((sigma : ℂ) + t * Complex.I)‖) / q.totient ≤ Fmean q X sigma u := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro chi hchi
  have hc := (mem_nonprincipalCharacters chi).mp hchi
  exact intervalIntegral.integral_mono_on (by linarith)
    (log_H_vertical_integrable hc X sigma u) (f_vertical_integrable hc X sigma u)
    (fun t _ => log_H_le_square chi X _)

def logSideDifference (q : ℕ) [NeZero q] (X sigma u : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -u..u,
    (Real.log ‖H chi X ((sigma : ℂ) + t * Complex.I)‖ -
      Real.log ‖H chi X ((2 : ℂ) + t * Complex.I)‖)) / q.totient

theorem logSideDifference_le (q : ℕ) [NeZero q] {X : ℝ} (hX : 5 ≤ X)
    (sigma : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    logSideDifference q X sigma u ≤
      Fmean q X sigma u + nonprincipalRatio q * (16 * u / (X - 1) ^ 2) := by
  have hs (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -u..u,
        (Real.log ‖H chi X ((sigma : ℂ) + t * Complex.I)‖ -
          Real.log ‖H chi X ((2 : ℂ) + t * Complex.I)‖)) ≤
      (∫ t in -u..u, ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) +
        16 * u / (X - 1) ^ 2 := by
    have hi := log_H_vertical_integrable hchi X sigma u
    have hr := log_H_vertical_integrable hchi X 2 u
    have h := intervalIntegral.integral_mono_on (by linarith : -u ≤ u) (hi.sub hr)
      ((f_vertical_integrable hchi X sigma u).add hr.abs) (fun t _ => by
        have hp := log_H_le_square chi X ((sigma : ℂ) + t * Complex.I)
        have hn := neg_le_abs (Real.log ‖H chi X ((2 : ℂ) + t * Complex.I)‖)
        norm_num only [Complex.ofReal_ofNat] at *
        linarith)
    rw [intervalIntegral.integral_add (f_vertical_integrable hchi X sigma u) hr.abs] at h
    exact h.trans (add_le_add le_rfl (abs_log_integral_two_le hchi hX hu))
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hs chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq (by
    unfold Fmean nonprincipalRatio
    ring)

theorem logSideDifference_PV (q : ℕ) [NeZero q] {X : ℝ} (hX : 5 ≤ X) {M : ℕ}
    (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma u : ℝ} (hs : sigma ∈ Set.Icc (1 / 2) 1) (hu : 0 ≤ u) :
    logSideDifference q X sigma u ≤
      pvBudget q X M sigma u + nonprincipalRatio q * (16 * u / (X - 1) ^ 2) :=
  (logSideDifference_le q hX sigma hu).trans
    (add_le_add (Fmean_PV_mother q X (by linarith) hNM hqN hs hu) le_rfl)

theorem logSideDifference_PV_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    logSideDifference q ((q : ℝ) * y) sigma y ≤
      pvBudget q ((q : ℝ) * y) M sigma y +
        nonprincipalRatio q * (16 * y / ((q : ℝ) * y - 1) ^ 2) := by
  by_cases hq : q ≤ 2
  · have hsmall : q = 1 ∨ q = 2 := by have := NeZero.pos q; omega
    rcases hsmall with rfl | rfl
    · simpa [logSideDifference, nonprincipalRatio] using
        pvBudget_nonneg 1 (1 * y) M sigma (by linarith : 0 ≤ y)
    · simpa [logSideDifference, nonprincipalRatio] using
        pvBudget_nonneg 2 (2 * y) M sigma (by linarith : 0 ≤ y)
  · have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr (show 3 ≤ q by omega)
    exact logSideDifference_PV q (by nlinarith) hNM (ceil_parameters q hy).2.1 hs (by linarith)

theorem logSideDifference_PV_unnormalized (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      (Real.log ‖H chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ -
        Real.log ‖H chi ((q : ℝ) * y) ((2 : ℂ) + t * Complex.I)‖)) ≤
      (q.totient : ℝ) *
        (pvBudget q ((q : ℝ) * y) M sigma y +
          nonprincipalRatio q * (16 * y / ((q : ℝ) * y - 1) ^ 2)) := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hp).mp (logSideDifference_PV_fixed_X q hy hs hNM)).trans_eq (mul_comm _ _)

theorem posLog_H_exponential_integrable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {sigma y : ℝ} (hs : 1 / 2 ≤ sigma) (hy : 0 < y) :
    Integrable (fun t : ℝ => Real.posLog ‖H chi X ((sigma : ℂ) + t * Complex.I)‖ *
      Real.exp (-|t| / y)) := by
  apply (exponential_strip_integrable hchi X hy hs).mono'
  · exact ((posLog_H_vertical_continuous hchi X sigma).mul
      (Real.continuous_exp.comp (continuous_id.abs.neg.div_const y))).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg Real.posLog_nonneg (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (posLog_H_le_square chi X _) (Real.exp_pos _).le

theorem posLog_H_axis_PV (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      Real.posLog ‖H chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ *
        Real.exp (-|t| / y)) / q.totient ≤ 16 * pvBudget q ((q : ℝ) * y) M sigma y := by
  apply le_trans _ (exponential_PV_fixed_X q hy hs hNM)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro chi hchi
  have hc := (mem_nonprincipalCharacters chi).mp hchi
  exact integral_mono (posLog_H_exponential_integrable hc _ hs.1 (by linarith))
    (exponential_strip_integrable hc _ (by linarith) hs.1) (fun t =>
      mul_le_mul_of_nonneg_right (posLog_H_le_square chi _ _) (Real.exp_pos _).le)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation
