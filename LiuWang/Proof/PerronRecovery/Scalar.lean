import LiuWang.Proof.PerronRecovery.Closed
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniform certificates on the original L >= 2000 domain. -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.PerronRecovery

open ExplicitPerron PerronBudget Interfaces Parameters

theorem exp_small_le : Real.exp (1 / 2000) ≤ 1.001 := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1 / 2000)
    (by norm_num : (1 / 2000 : ℝ) ≤ 1) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem two_rpow_source_le {L : ℝ} (hL : 2000 ≤ L) :
    (2 : ℝ) ^ (1 + 1 / L) ≤ 2.002 := by
  have hL0 : 0 < L := by linarith
  have he : Real.log 2 * (1 / L) ≤ 1 / 2000 := by
    rw [mul_one_div]
    exact (div_le_iff₀ hL0).mpr (by linarith [log_two_bounds.2])
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := (Real.exp_le_exp.mpr he).trans exp_small_le
  linarith

theorem rpow_small_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    x ^ (1 / sourceL N) ≤ 3 := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have he : Real.log x * (1 / sourceL N) ≤ 1 + 1 / 2000 := by
    rw [mul_one_div]
    exact (div_le_iff₀ hL0).mpr (by
      linarith [(source_log_bounds hN hx hxN).2.1])
  have hexp : Real.exp 1 ≤ 2.72 := by
    have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  calc
    _ = Real.exp (Real.log x * (1 / sourceL N)) := Real.rpow_def_of_pos (by linarith) _
    _ ≤ Real.exp (1 + 1 / 2000) := Real.exp_le_exp.mpr he
    _ = Real.exp 1 * Real.exp (1 / 2000) := Real.exp_add _ _
    _ ≤ 2.72 * 1.001 := mul_le_mul hexp exp_small_le (Real.exp_pos _).le (by norm_num)
    _ ≤ 3 := by norm_num

theorem rpow_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    x ^ (1 + 1 / sourceL N) ≤ 3 * x := by
  rw [Real.rpow_add (by linarith : 0 < x), Real.rpow_one]
  nlinarith [mul_le_mul_of_nonneg_left (rpow_small_source_le hN hx hxN)
    (by linarith : 0 ≤ x)]

theorem series_factor_source_le {L : ℝ} (hL : 2000 ≤ L) :
    L + 8 ≤ 1.004 * L ∧ (L + 8) / Real.pi ≤ 0.32 * L := by
  have hL0 : 0 < L := by linarith
  refine ⟨by linarith, (div_le_iff₀ Real.pi_pos).mpr ?_⟩
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_d4.le
    (show 0 ≤ 0.32 * L by positivity)
  nlinarith

theorem halfError_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {x : ℝ} (hx : 1 ≤ x) (hxN : x ≤ 2 * (N : ℝ)) :
    halfError x (1 + 1 / sourceL N) (sourceT N) (sourceL N + 8) ≤
      0.96 * x / sourceT N * sourceL N ^ (2 : ℕ) := by
  let L := sourceL N
  have hL : 2000 ≤ L := sourceL_ge_2000 hN
  have hL0 : 0 < L := sourceL_pos hN
  have hT0 := sourceT_pos hN
  have hx0 : 0 < x := by linarith
  have hLL : 2000 * L ≤ L ^ (2 : ℕ) := by nlinarith
  have hC := (series_factor_source_le hL).1
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_bounds.1]
  have hdiv : x ^ (1 + 1 / L) / Real.log 2 ≤ 6 * x := by
    apply (div_le_iff₀ hlog2).mpr
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.1 (show 0 ≤ 6 * x by positivity)
    nlinarith [rpow_source_le hN hx hxN]
  have hspectral : x ^ (1 + 1 / L) / Real.log 2 * (L + 8) ≤
      0.00302 * x * L ^ (2 : ℕ) := by
    have hc : 6 * (1.004 * L) ≤ 0.00302 * L ^ (2 : ℕ) := by nlinarith
    calc
      _ ≤ (6 * x) * (1.004 * L) := mul_le_mul hdiv hC (by positivity) (by positivity)
      _ = x * (6 * (1.004 * L)) := by ring
      _ ≤ x * (0.00302 * L ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hc hx0.le
      _ = _ := by ring
  obtain ⟨hlx0, hlx, hl2x0, hl2x⟩ := source_log_bounds hN hx hxN
  change Real.log x ≤ L + 1 at hlx
  change Real.log (2 * x) ≤ L + 2 at hl2x
  have ha : Real.log x ≤ 1.0005 * L := by linarith
  have ha3 : Real.log x + 3 ≤ 1.002 * L := by linarith
  have hb : Real.log (2 * x) ≤ 1.001 * L := by linarith
  have hb3 : Real.log (2 * x) + 3 ≤ 1.0025 * L := by linarith
  have hpoly :
      2 ^ (1 + 1 / L) * Real.log x * (Real.log x + 3) +
        Real.log (2 * x) * (Real.log (2 * x) + 3) ≤ 3.011 * L ^ (2 : ℕ) := by
    calc
      _ ≤ 2.002 * (1.0005 * L) * (1.002 * L) + (1.001 * L) * (1.0025 * L) := by
        gcongr
        exact two_rpow_source_le hL
      _ ≤ _ := by nlinarith [sq_nonneg L]
  have hnum :
      x ^ (1 + 1 / L) / Real.log 2 * (L + 8) +
        x * (2 ^ (1 + 1 / L) * Real.log x * (Real.log x + 3) +
          Real.log (2 * x) * (Real.log (2 * x) + 3)) ≤ 3.01402 * x * L ^ (2 : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_left hpoly hx0.le]
  change (_ + _) / (Real.pi * sourceT N) ≤ 0.96 * x / sourceT N * L ^ (2 : ℕ)
  calc
    _ ≤ (3.01402 * x * L ^ (2 : ℕ)) / (Real.pi * sourceT N) := by gcongr
    _ = (3.01402 / Real.pi) * (x / sourceT N * L ^ (2 : ℕ)) := by ring
    _ ≤ 0.96 * (x / sourceT N * L ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_iff₀ Real.pi_pos).mpr
      linarith [Real.pi_gt_d4]
    _ = _ := by ring

end LiuWang.Proof.PerronRecovery
