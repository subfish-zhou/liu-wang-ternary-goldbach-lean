import LiuWang.Proof.PrincipalPsi.Quantitative.BoundaryIntegrals
import LiuWang.Proof.PrincipalPsi.Quantitative.ClosedTransport
import LiuWang.Proof.FixedHeightZeroSum.Budget

/-! # 原实端点域中的独立数值付款 -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.NonSymmetricContour
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem source_log_height_shift {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    Real.log (sourceT N + 3) ≤ 3 / 50 * sourceL N + 1 := by
  have hT := sourceT_pos hN
  have hT3 : 3 ≤ sourceT N :=
    (by norm_num : (3 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans (sourceT_large hN)
  have h := Real.log_le_log (by positivity : 0 < sourceT N + 3)
    (show sourceT N + 3 ≤ 2 * sourceT N by linarith)
  rw [Real.log_mul (by norm_num) hT.ne'] at h
  have he : Real.log (sourceT N) = 15 * Real.log (sourceL N) := by
    simp [sourceT, Real.log_pow]
  rw [he] at h
  linarith [log_le_div_250 (sourceL_ge_2000 hN),
    Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem source_referenceMass_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    referenceMass (sourceT N) ≤ 17 / 500 * sourceL N := by
  have hlog := source_log_height_shift hN
  have hlog' := Real.log_le_log (by linarith [sourceT_pos hN] : 0 < sourceT N + 2)
    (show sourceT N + 2 ≤ sourceT N + 3 by linarith)
  unfold referenceMass
  rw [abs_of_pos (sourceT_pos hN)]
  linarith [sourceL_ge_2000 hN]

theorem source_horizontalLogBound_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {H : ℝ} (hH : |(|H|) - sourceT N| ≤ 1) :
    horizontalLogBound H (heightSeparationBudget (sourceT N)) ≤ sourceL N ^ 2 / 2 := by
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hh := (abs_le.mp hH).2
  have hlog : Real.log (|H| + 2) ≤ 3 / 50 * sourceL N + 1 :=
    (Real.log_le_log (by positivity) (by linarith : |H| + 2 ≤ sourceT N + 3)).trans
      (source_log_height_shift hN)
  have hM : referenceMass H ≤ sourceL N / 10 := by
    unfold referenceMass
    linarith
  have hB : heightSeparationBudget (sourceT N) ≤ sourceL N / 2 + 1 := by
    unfold heightSeparationBudget
    linarith [source_referenceMass_le hN]
  have hprod := mul_le_mul
    (show 5 / 2 + (5 / 2 : ℝ)^2 * heightSeparationBudget (sourceT N) ≤
      5 / 2 + (5 / 2 : ℝ)^2 * (sourceL N / 2 + 1) by nlinarith)
    hM (referenceMass_nonneg H) (by positivity)
  unfold horizontalLogBound
  have hsq := mul_le_mul_of_nonneg_right hL hL0.le
  nlinarith

theorem source_horizontal_power_cost {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ)) :
    t ^ (1 + 1 / sourceL N) / Real.log t + 7 * (1 + 1 / sourceL N + 1 / 2) ≤ t / 600 := by
  obtain ⟨_, htbig, hlog, _, _, hb, hpow⟩ :=
    HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  have hdiv : t ^ (1 + 1 / sourceL N) / Real.log t ≤ (3 / 1990 : ℝ) * t := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log t)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (3 / 1990 : ℝ) * t by positivity)
    linarith
  linarith [HorizontalEstimate.source_endpoint_ge_billion hN htlo]

theorem norm_horizontal_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t H : ℝ} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : ℝ))
    (hH : |(|H|) - sourceT N| ≤ 1)
    (hsep : ∀ p : RiemannXiDivisorZeroIndex,
      (heightSeparationBudget (sourceT N))⁻¹ ≤ |(riemannXiDivisorZeroValue p).im - H|) :
    ‖horizontalIntegral (zetaCenteredIntegrand t) (1 + 1 / sourceL N) H‖ ≤
      0.0003 * t / sourceT N * sourceL N ^ 2 := by
  obtain ⟨_, htbig, _, _, hb, hb2, _⟩ :=
    HorizontalEstimate.source_horizontal_parameters hN htlo hthi
  have hT := sourceT_pos hN
  have hT4 : 4 ≤ sourceT N :=
    (by norm_num : (4 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans (sourceT_large hN)
  have hh := (abs_le.mp hH).1
  have hHa : 2 ≤ |H| := by linarith
  have hH0 : 0 < |H| := by linarith
  have hinv : 1 / |H| ≤ 2 / sourceT N := by
    apply (div_le_div_iff₀ hH0 hT).mpr
    linarith
  have hraw := norm_zeta_horizontal_le (by linarith : 1 < t) hb (by linarith)
    (heightSeparationBudget_pos _) hHa hsep
  have hD := source_horizontalLogBound_le hN hH
  have hK := source_horizontal_power_cost hN htlo hthi
  have hK0 : 0 ≤ t ^ (1 + 1 / sourceL N) / Real.log t +
      7 * (1 + 1 / sourceL N + 1 / 2) := by
    have ht0 : 0 < t := by linarith
    have hl := Real.log_pos (show 1 < t by linarith)
    positivity
  have hi : horizontalLogBound H (heightSeparationBudget (sourceT N)) / |H| ≤
      sourceL N ^ 2 / sourceT N := by
    calc
      _ ≤ (sourceL N ^ 2 / 2) * (2 / sourceT N) :=
        by simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul hD hinv (by positivity) (by positivity)
      _ = _ := by ring
  have hn : horizontalLogBound H (heightSeparationBudget (sourceT N)) / |H| *
      (t ^ (1 + 1 / sourceL N) / Real.log t + 7 * (1 + 1 / sourceL N + 1 / 2)) ≤
      (sourceL N ^ 2 / sourceT N) * (t / 600) :=
    mul_le_mul hi hK hK0 (by positivity)
  apply hraw.trans
  calc
    _ ≤ ((sourceL N ^ 2 / sourceT N) * (t / 600)) / 6 :=
      div_le_div₀ (by positivity) hn (by norm_num) (by linarith [Real.pi_gt_three])
    _ = (1 / 3600 : ℝ) * (t / sourceT N * sourceL N ^ 2) := by ring
    _ ≤ 0.0003 * (t / sourceT N * sourceL N ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

theorem transport_cost_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    10 * referenceMass (sourceT N) * ((t + 2.5) / (sourceT N - 1)) ≤
      0.00035 * t / sourceT N * sourceL N ^ 2 := by
  have hT := sourceT_pos hN
  have hT10 : 10 ≤ sourceT N :=
    (by norm_num : (10 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans (sourceT_large hN)
  have htT := sourceT_lt_real_endpoint hN htlo
  have ht0 : 0 < t := by linarith
  have hTm0 : 0 < sourceT N - 1 := by linarith
  have hk : (t + 2.5) / (sourceT N - 1) ≤ 2 * (t / sourceT N) := by
    apply (div_le_iff₀ (by linarith : 0 < sourceT N - 1)).mpr
    have he : 2 * (t / sourceT N) * (sourceT N - 1) = 2 * t - 2 * (t / sourceT N) := by
      field_simp
    rw [he]
    have hd : t / sourceT N ≤ t / 10 := div_le_div_of_nonneg_left ht0.le (by norm_num) hT10
    linarith
  have hL := sourceL_ge_2000 hN
  have hL0 := sourceL_pos hN
  have hc : (10 * (17 / 500 : ℝ) * 2) * sourceL N ≤ 0.00035 * sourceL N ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hL (sourceL_pos hN).le
    nlinarith
  calc
    _ ≤ (10 * (17 / 500 : ℝ) * sourceL N) * (2 * (t / sourceT N)) :=
      mul_le_mul (by linarith [source_referenceMass_le hN]) hk (by positivity) (by positivity)
    _ = ((10 * (17 / 500 : ℝ) * 2) * sourceL N) * (t / sourceT N) := by ring
    _ ≤ (0.00035 * sourceL N ^ 2) * (t / sourceT N) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem low_center_cost_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    (2 * Real.sqrt t + 5) * ((2 / 3 : ℝ) * sourceT N ^ 2) ≤
      0.000001 * t / sourceT N * sourceL N ^ 2 := by
  have hL0 := sourceL_pos hN
  have hL1 := one_le_sourceL hN
  have hT0 := sourceT_pos hN
  have ht0 : 0 < t := hT0.trans (sourceT_lt_real_endpoint hN htlo)
  have hs := FixedHeightZeroSum.source_sqrt_endpoint_ge_hundred_million_power hN htlo
  have hp : 1 ≤ sourceL N ^ (44 : ℕ) := one_le_pow₀ hL1
  have hs1 : 1 ≤ Real.sqrt t := by linarith
  have hc : (2 * Real.sqrt t + 5) * ((2 / 3 : ℝ) * sourceT N ^ 2) ≤
      5 * Real.sqrt t * sourceT N ^ 2 :=
    by nlinarith [mul_nonneg (show 0 ≤ Real.sqrt t - 1 by linarith) (sq_nonneg (sourceT N))]
  have hpay : 5 * sourceT N ^ 3 ≤ 0.000001 * Real.sqrt t * sourceL N := by
    have hh := mul_le_mul_of_nonneg_right hs hL0.le
    have he : sourceL N ^ (44 : ℕ) * sourceL N = sourceT N ^ 3 := by unfold sourceT; ring
    have hh' : 100000000 * sourceT N ^ 3 ≤ Real.sqrt t * sourceL N := by
      calc
        _ = (100000000 * sourceL N ^ (44 : ℕ)) * sourceL N := by rw [mul_assoc, he]
        _ ≤ _ := hh
    nlinarith [pow_nonneg hT0.le 3]
  apply hc.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT0).mpr
  have hh := mul_le_mul_of_nonneg_right hpay (Real.sqrt_nonneg t)
  have hl := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 0.000001 * t * sourceL N by positivity)
  nlinarith [Real.sq_sqrt ht0.le]

theorem polynomial_left_cost_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    120 * sourceT N ^ 3 ≤ 0.000001 * t / sourceT N * sourceL N ^ 2 := by
  have hL1 := one_le_sourceL hN
  have hT0 := sourceT_pos hN
  have ht0 : 0 < t := hT0.trans (sourceT_lt_real_endpoint hN htlo)
  have hs := FixedHeightZeroSum.source_sqrt_endpoint_ge_hundred_million_power hN htlo
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ 100000000 * sourceL N ^ (44 : ℕ)) hs 2
  rw [Real.sq_sqrt ht0.le] at hs2
  have hp : sourceL N ^ (60 : ℕ) ≤ sourceL N ^ (88 : ℕ) :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hpay : 120 * sourceT N ^ 4 ≤ 0.000001 * t := by
    have he : sourceT N ^ 4 = sourceL N ^ (60 : ℕ) := by unfold sourceT; ring
    rw [he]
    nlinarith [pow_nonneg (sourceL_pos hN).le 60]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hT0).mpr
  have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hL1 : 1 ≤ sourceL N ^ 2)
    (show 0 ≤ 0.000001 * t by positivity)
  nlinarith

theorem norm_left_source_le {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    {t Hp Hm : ℝ} (htlo : sourceWindowLower N ≤ t)
    (hp : |Hp - sourceT N| ≤ 1) (hm : |Hm + sourceT N| ≤ 1) :
    ‖verticalIntegral (zetaCenteredIntegrand t) (-1 / 2) Hp Hm‖ ≤
      0.000001 * t / sourceT N * sourceL N ^ 2 := by
  have hT3 : 3 ≤ sourceT N :=
    (by norm_num : (3 : ℝ) ≤ 2000 ^ (15 : ℕ)).trans (sourceT_large hN)
  have hpp := abs_le.mp hp
  have hmm := abs_le.mp hm
  have hpa : |Hp| ≤ sourceT N + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hma : |Hm| ≤ sourceT N + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hd : |Hp - Hm| ≤ 3 * sourceT N := abs_le.mpr ⟨by linarith, by linarith⟩
  have ht := HorizontalEstimate.source_endpoint_ge_billion hN htlo
  apply (norm_zeta_vertical_le (by linarith : 9 ≤ t) hma hpa).trans
  apply le_trans _ (polynomial_left_cost_source_le hN htlo)
  have hs : (sourceT N + 1 + 2) ^ 2 ≤ (2 * sourceT N) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hnum := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 60))
    hd (abs_nonneg _) (by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  have hpi := mul_le_mul_of_nonneg_left (show 6 ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
    (show 0 ≤ 120 * sourceT N ^ 3 by positivity)
  nlinarith

end LiuWang.Proof.PrincipalPsi.Quantitative
