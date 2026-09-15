import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.AbelMean

/-! Strict ordered truncations converge to the actual L and f; the PV mean-square error vanishes. -/

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

theorem partialL_tendsto {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => partialL chi M s) atTop (𝓝 (chi.LFunction s)) := by
  have h := DirichletLConditionalValueSeries.tendsto_sum_range_orderedValueSeries chi hchi s hs
  rw [DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos chi hchi s hs] at h
  simpa only [partialL_eq_Abel_sum hchi] using h

theorem finiteDetector_tendsto {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => finiteDetector chi X M s) atTop
      (𝓝 (NonprincipalDensityAdvance.f chi X s)) :=
  ((partialL_tendsto hchi hs).mul_const (NonprincipalDensityAdvance.Q chi X s)).sub_const 1

theorem remainderMean_tendsto_zero (q : ℕ) [NeZero q] (X : ℝ)
    {sigma u : ℝ} (hs : 1 / 2 ≤ sigma) (hu : 0 ≤ u) :
    Tendsto (fun M : ℕ => remainderMean q X M sigma u) atTop (𝓝 0) := by
  let C := 4 * prefixBudget q ^ 2 * (1 + u) ^ 2 * mollifierMeanBound q X u
  have hlim : Tendsto (fun M : ℕ => C / (M : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  apply squeeze_zero' (Filter.Eventually.of_forall (fun M => remainderMean_nonneg q X M sigma hu)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact remainderMean_le_reciprocal q X hM hs hu

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation
