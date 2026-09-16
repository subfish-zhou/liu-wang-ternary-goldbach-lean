import LiuWang.Proof.Campaign20260915.ZetaRealNormalization.ActualC2Normalization

set_option autoImplicit false
noncomputable section
open Complex

namespace LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaRealNormalization
open LiuWang.Proof.Campaign20260915.ZetaMordell

theorem inverse_sqrt_step (n : ℕ) :
    (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * Real.sqrt (n + 1) - 2 * Real.sqrt n := by
  have hb : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have ha2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hb2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, inv_eq_one_div,
    div_le_iff₀ hb]
  nlinarith [sq_nonneg (Real.sqrt (n + 1) - Real.sqrt (n : ℝ))]

theorem inverse_sqrt_sum_budget {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ Finset.range m, (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * Real.sqrt m - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  clear hm
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := inverse_sqrt_step (m + 1)
    push_cast at ih h ⊢
    linarith

theorem sourceRealMainSum_abs_budget (t : ℝ) {m : ℕ} (hm : 0 < m) :
    |sourceRealMainSum t m| ≤ 4 * Real.sqrt m - 2 := by
  have hsum :
      |∑ n ∈ Finset.range m,
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.cos (criticalGammaArgument t - t * Real.log (n + 1))| ≤
        ∑ n ∈ Finset.range m, (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro n _
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
      (Real.abs_cos_le_one _)
  unfold sourceRealMainSum
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [inverse_sqrt_sum_budget hm]

theorem four_sqrt_le_source_K {eta : ℝ} (he : 0 ≤ eta) :
    4 * Real.sqrt eta ≤ (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) := by
  have ht : 0 ≤ sourceTime eta := by unfold sourceTime; positivity
  have hp : (sourceTime eta ^ (1 / 4 : ℝ)) ^ 4 = sourceTime eta := by
    rw [← Real.rpow_mul_natCast ht]
    norm_num
  have he2 := Real.sq_sqrt he
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
  rw [mul_pow, mul_pow, hp,
    show (Real.sqrt eta) ^ 4 = ((Real.sqrt eta) ^ 2) ^ 2 by ring, he2]
  have hpi : (256 : ℝ) ≤ (253 / 100 : ℝ) ^ 4 * (2 * Real.pi) := by
    nlinarith [Real.pi_gt_d2]
  have h := mul_le_mul_of_nonneg_right hpi (sq_nonneg eta)
  unfold sourceTime
  rw [mul_pow, rsSaddleScale_sq]
  nlinarith

theorem sourceHeightScale_original_lower {t : ℝ} (ht : 128 * Real.pi ≤ t) :
    8 ≤ sourceHeightScale t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have he := Real.sq_sqrt (le_of_lt (div_pos ht0 (by positivity : 0 < 2 * Real.pi)))
  have hr : (64 : ℝ) ≤ t / (2 * Real.pi) :=
    (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by linarith)
  unfold sourceHeightScale
  nlinarith [Real.sqrt_nonneg (t / (2 * Real.pi))]

theorem sourceRealMainSum_original_margin {t : ℝ} (ht : 128 * Real.pi ≤ t) :
    |sourceRealMainSum t ⌊sourceHeightScale t⌋₊| ≤
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) - 2 := by
  have he := sourceHeightScale_original_lower ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hm := Nat.floor_pos.mpr (show 1 ≤ sourceHeightScale t by linarith)
  have hmain := sourceRealMainSum_abs_budget t hm
  have hs := Real.sqrt_le_sqrt (Nat.floor_le (by linarith : 0 ≤ sourceHeightScale t))
  have hK := four_sqrt_le_source_K (by linarith : 0 ≤ sourceHeightScale t)
  rw [sourceTime_heightScale ht0.le] at hK
  linarith

theorem norm_zeta_original_main_margin {t : ℝ} (ht : 128 * Real.pi ≤ t) :
    ‖riemannZeta (criticalPoint t)‖ ≤
      (253 / 100 : ℝ) * t ^ (1 / 4 : ℝ) - 2 +
        |normalizedCriticalZeta t - sourceRealMainSum t ⌊sourceHeightScale t⌋₊| := by
  have h := abs_add_le
    (sourceRealMainSum t ⌊sourceHeightScale t⌋₊)
    (normalizedCriticalZeta t - sourceRealMainSum t ⌊sourceHeightScale t⌋₊)
  rw [add_sub_cancel, abs_normalizedCriticalZeta] at h
  linarith [sourceRealMainSum_original_margin ht]

theorem norm_zeta_original_C2_growth_budget {eta : ℝ}
    (he : 8 ≤ eta) (hint : ∀ k : ℤ, eta ≠ k) :
    ‖riemannZeta (criticalPoint (sourceTime eta))‖ ≤
      (253 / 100 : ℝ) * (sourceTime eta) ^ (1 / 4 : ℝ) - 2 +
        |sourceCentralNormalized eta| + |sourceLeftNormalized eta| +
          |sourceRightNormalized eta| := by
  have hf := sourceFraction_floor (by linarith : 0 ≤ eta) hint
  have hm := Nat.floor_pos.mpr (show 1 ≤ eta by linarith)
  have hmain := sourceRealMainSum_abs_budget (sourceTime eta) hm
  have hs := Real.sqrt_le_sqrt (Nat.floor_le (by linarith : 0 ≤ eta))
  have hK := four_sqrt_le_source_K (by linarith : 0 ≤ eta)
  have hz := normalized_zeta_C2_exact hm hf.1 hf.2
  rw [← abs_normalizedCriticalZeta, hz]
  have h := (abs_sub
    (sourceRealMainSum (sourceTime eta) ⌊eta⌋₊ +
      sourceCentralNormalized eta + sourceLeftNormalized eta)
    (sourceRightNormalized eta)).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  linarith

#print axioms inverse_sqrt_sum_budget
#print axioms sourceRealMainSum_original_margin
#print axioms norm_zeta_original_main_margin
#print axioms norm_zeta_original_C2_growth_budget

end LiuWang.Proof.Campaign20260915.ZetaTuringLogBudgets
