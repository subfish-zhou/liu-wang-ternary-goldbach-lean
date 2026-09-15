import LiuWang.Proof.SourceRoute.SecondArc.OriginalIntegrals
import LiuWang.Proof.NearOneDensity.Continuation.CountInterface
import LiuWang.Proof.CompleteExpansion.Consumer

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

theorem source_S_is_Lambda (N : ℕ) (alpha : ℝ) :
    S N alpha = ∑ n ∈ windowFinset N,
      (ArithmeticFunction.vonMangoldt n : ℂ) * charReal ((n : ℝ) * alpha) :=
  LiuWang.Proof.CompleteExpansion.S_eq_closed_sum N alpha

theorem exact_scale_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    1 ≤ y ∧ 100000000000 ≤ (q : ℝ) * y ∧
      (q : ℝ) * max 1 y ≤ (q : ℝ) * y := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlo : 3.36 ≤ y := (omegaCutoff_ge (NeZero.pos q) hq).trans hy
  have hy1 : 1 ≤ y := by linarith
  have hprod : 3.36 * sourceL N ^ (3 : ℕ) ≤ (q : ℝ) * y := by
    have h := (div_le_iff₀ hq0).mp hy
    simpa only [mul_comm, sourceP] using h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) (sourceL_ge_3100 hN) 3
  refine ⟨hy1, ?_, by rw [max_eq_right hy1]⟩
  nlinarith

theorem actual_familyCount_14000 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y alpha : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 1 - (0.478 : ℝ) / Real.log ((q : ℝ) * y) ≤ alpha) :
    (familyCount q alpha y : ℝ) ≤ 14000 := by
  have hd := exact_scale_domain hN hq hy
  have hc := LiuWang.Proof.NearOneDensity.Continuation.familyCount_row_tail
    .r0478 hd.2.1 hd.2.2 ha
  norm_num [LiuWang.Proof.NearOneDensity.rowBound,
    LiuWang.Proof.NearOneDensity.rowMultiplicity,
    LiuWang.Proof.NearOneDensity.rowSelectedBound] at hc
  exact_mod_cast hc

theorem strip_order {q : ℕ} [NeZero q] {y : ℝ} (hy : 1 ≤ y) :
    1 - (0.478 : ℝ) / Real.log ((q : ℝ) * y) ≤
      1 - (0.2067 : ℝ) / Real.log ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hl : 0 ≤ Real.log ((q : ℝ) * y) :=
    Real.log_nonneg (by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hy)])
  have h := div_le_div_of_nonneg_right (by norm_num : (0.2067 : ℝ) ≤ 0.478) hl
  linarith

theorem actual_inner_516 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (∫ alpha in (1 - (0.478 : ℝ) / Real.log ((q : ℝ) * y))..
      (1 - (0.2067 : ℝ) / Real.log ((q : ℝ) * y)),
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      14000 * (Real.exp (-0.2067 * Real.log (0.001 * (N : ℝ)) /
          Real.log ((q : ℝ) * y)) -
        Real.exp (-0.478 * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y))) := by
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hh := strip_order (q := q) (exact_scale_domain hN hq hy).1
  calc
    _ ≤ ∫ alpha in (1 - (0.478 : ℝ) / Real.log ((q : ℝ) * y))..
        (1 - (0.2067 : ℝ) / Real.log ((q : ℝ) * y)),
          14000 * alphaKernel (0.001 * (N : ℝ)) alpha := by
      apply intervalIntegral.integral_mono_on hh
        (count_alpha_integrable hx hh y)
        (((continuous_alphaKernel hx).const_mul 14000).intervalIntegrable _ _)
      intro alpha ha
      have hk : 0 ≤ alphaKernel (0.001 * (N : ℝ)) alpha :=
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (window_base_ge_one hN))
      exact (mul_le_mul_of_nonneg_left (actual_familyCount_14000 hN hq hy ha.1) hk).trans_eq
        (mul_comm _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, source_515_first_strip hx]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
