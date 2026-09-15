import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Integral

/-!
# 在实部 `3/4` 处分段支付原文预算

右段消费较短参考距离产生的 `5/2 log²(qT)` 界；左段仍完整积分，
利用 `t^(3/4)` 的衰减。每条边的预算为 `0.0042 t/T log²(qT)`。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

theorem source_endpoint_ge_billion {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t : Real}
    (htlo : sourceWindowLower N ≤ t) :
    1000000000 ≤ t := by
  have hT : (2000 : Real) ^ (15 : Nat) ≤ sourceT N := by
    unfold sourceT
    gcongr
    exact sourceL_ge_2000 hN
  have ht := sourceT_lt_real_endpoint hN htlo
  have hn : (1000000000 : Real) ≤ 2000 ^ (15 : Nat) := by norm_num
  linarith

theorem source_left_power_le {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t σ : Real}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real))
    (hσ : σ ≤ (3 : Real) / 4) :
    t ^ σ + 7 ≤ t / 100000 := by
  obtain ⟨_, htbig, hlog, _, _, _, _⟩ := source_horizontal_parameters hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hlarge := source_endpoint_ge_billion hN htlo
  have hmil : Real.log 1000000 ≤ 54 := by
    have he := Real.log_pow (10 : Real) 6
    norm_num at he
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 10)
    linarith
  have hquarter : (1000000 : Real) ≤ t ^ (1 / 4 : Real) := by
    rw [Real.rpow_def_of_pos ht0]
    have he := Real.exp_le_exp.mpr
      (show Real.log 1000000 ≤ Real.log t * (1 / 4) by linarith)
    simpa only [Real.exp_log (by norm_num : (0 : Real) < 1000000)] using he
  have hprod : t ^ (3 / 4 : Real) * t ^ (1 / 4 : Real) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have hsmall : t ^ (3 / 4 : Real) ≤ t / 1000000 := by
    have hm := mul_le_mul_of_nonneg_left hquarter
      (Real.rpow_nonneg ht0.le (3 / 4 : Real))
    rw [hprod] at hm
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ t by linarith) hσ
  linarith

theorem source_right_power_integral_le {N : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) {t : Real}
    (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    (∫ σ in (3 / 4 : Real)..(1 + 1 / sourceL N), (t ^ σ + 7)) ≤ t / 650 := by
  obtain ⟨_, htbig, hlog, _, _, hb2, hpow⟩ := source_horizontal_parameters hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < Real.log t := by linarith
  have hlarge := source_endpoint_ge_billion hN htlo
  have heq : (∫ σ in (3 / 4 : Real)..(1 + 1 / sourceL N), t ^ σ) =
      (t ^ (1 + 1 / sourceL N) - t ^ (3 / 4 : Real)) / Real.log t := by
    simp_rw [Real.rpow_def_of_pos ht0]
    rw [intervalIntegral.integral_comp_mul_left Real.exp hl0.ne', integral_exp]
    simp only [smul_eq_mul]
    ring
  have hi : (∫ σ in (3 / 4 : Real)..(1 + 1 / sourceL N), t ^ σ) ≤
      (3 / 1990 : Real) * t := by
    rw [heq]
    apply (div_le_iff₀ hl0).mpr
    have hn := Real.rpow_nonneg ht0.le (3 / 4 : Real)
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (3 / 1990 : Real) * t by positivity)
    nlinarith
  rw [intervalIntegral.integral_add
    ((Real.continuous_const_rpow ht0.ne').intervalIntegrable _ _) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  linarith

theorem norm_horizontal_integral_source_sharp_le
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t H : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real))
    (hH : |(|H|) - sourceT N| ≤ 1)
    (hsep : ∀ p : CompletedZeroIndex chi,
      (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
        |(completedZeroValue p).im - H|) :
    ‖∫ σ in (-(1 : Real) / 2)..(1 + 1 / sourceL N),
      horizontalIntegrand chi t ((σ : Complex) + (H : Complex) * Complex.I)‖ ≤
      (21 / 5000 : Real) * t / sourceT N *
        (Real.log ((q : Real) * sourceT N)) ^ 2 := by
  obtain ⟨hT, htbig, _, _, hb1, hb2, _⟩ := source_horizontal_parameters hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hT0 := sourceT_pos hN
  have habs := source_height_abs_bounds hT hH
  have hH0 : 0 < |H| := by linarith [habs.1]
  have hHne : H ≠ 0 := abs_pos.mp hH0
  have hB := source_height_budget_pos hq hT
  have hT100 : 100 ≤ sourceT N :=
    (by norm_num : (100 : Real) ≤ 2000 ^ (15 : Nat)).trans hT
  have hlower : (99 / 100 : Real) * sourceT N ≤ |H| := by
    have hh := (abs_le.mp hH).1
    linarith
  have hinv : 1 / |H| ≤ 1 / ((99 / 100 : Real) * sourceT N) :=
    one_div_le_one_div_of_le (by positivity) hlower
  let L := Real.log ((q : Real) * sourceT N)
  let f : Real → Complex := fun σ =>
    horizontalIntegrand chi t ((σ : Complex) + (H : Complex) * Complex.I)
  have hscale : 0 ≤ t / sourceT N * L ^ 2 := by positivity
  have hcont := continuousOn_horizontalIntegrand hchi hPrimitive ht0 hB hHne hsep
    (b := 1 + 1 / sourceL N)
  have hil : IntervalIntegrable f volume (-(1 : Real) / 2) (3 / 4) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (continuousOn_horizontalIntegrand hchi hPrimitive ht0 hB hHne hsep)
  have hir : IntervalIntegrable f volume (3 / 4) (1 + 1 / sourceL N) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith)
      (hcont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl))
  have hleft : ‖∫ σ in (-(1 : Real) / 2)..(3 / 4 : Real), f σ‖ ≤
      (1 / 5000 : Real) * t / sourceT N * L ^ 2 := by
    have hm : ∀ σ ∈ Set.uIoc (-(1 : Real) / 2) (3 / 4 : Real),
        ‖f σ‖ ≤ (10 * L ^ 2) / |H| * (t / 100000) := by
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      have hslo : -(1 : Real) / 2 ≤ ((σ : Complex) + (H : Complex) * Complex.I).re := by
        simpa using hσ.1.le
      have hshi : ((σ : Complex) + (H : Complex) * Complex.I).re ≤ 2 := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hσ.2]
      have hd := norm_logDeriv_source_height_le hq hchi hPrimitive hT hH hsep
        (by simp) hslo hshi
      have hp := norm_horizontalIntegrand_le_power chi ht0 hshi
        (by simpa using hH0) hd
      have hp' : ‖f σ‖ ≤ 10 * L ^ 2 / |H| * (t ^ σ + 7) := by
        simpa [f, L] using hp
      exact hp'.trans (mul_le_mul_of_nonneg_left
        (source_left_power_le hN htlo hthi hσ.2) (by positivity))
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hm
    rw [show |(3 / 4 : Real) - (-(1 : Real) / 2)| = 5 / 4 by norm_num] at hi
    have hx := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ (10 * L ^ 2) * (t / 100000) * (5 / 4) by positivity)
    calc
      _ ≤ (10 * L ^ 2) / |H| * (t / 100000) * (5 / 4) := hi
      _ = ((10 * L ^ 2) * (t / 100000) * (5 / 4)) * (1 / |H|) := by ring
      _ ≤ ((10 * L ^ 2) * (t / 100000) * (5 / 4)) *
          (1 / ((99 / 100 : Real) * sourceT N)) := hx
      _ = (1 / 7920 : Real) * (t / sourceT N * L ^ 2) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      _ ≤ (1 / 5000 : Real) * (t / sourceT N * L ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hscale
      _ = _ := by ring
  have hright : ‖∫ σ in (3 / 4 : Real)..(1 + 1 / sourceL N), f σ‖ ≤
      (1 / 250 : Real) * t / sourceT N * L ^ 2 := by
    have hm : ∀ σ ∈ Set.Ioc (3 / 4 : Real) (1 + 1 / sourceL N),
        ‖f σ‖ ≤ ((5 / 2 : Real) * L ^ 2) / |H| * (t ^ σ + 7) := by
      intro σ hσ
      have hslo : (3 : Real) / 4 ≤ ((σ : Complex) + (H : Complex) * Complex.I).re := by
        simpa using hσ.1.le
      have hshi : ((σ : Complex) + (H : Complex) * Complex.I).re ≤ 2 := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hσ.2]
      have hd := norm_logDeriv_source_height_right_le hq hchi hPrimitive hT hH hsep
        (by simp) hslo hshi
      have hp := norm_horizontalIntegrand_le_power chi ht0 hshi
        (by simpa using hH0) hd
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add] using hp
    have hc : Continuous (fun σ : Real => ((5 / 2 : Real) * L ^ 2) / |H| * (t ^ σ + 7)) :=
      continuous_const.mul ((Real.continuous_const_rpow ht0.ne').add continuous_const)
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (by linarith : (3 / 4 : Real) ≤ 1 + 1 / sourceL N)
      (Filter.Eventually.of_forall hm) (hc.intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hi
    have hmaj := mul_le_mul_of_nonneg_left (source_right_power_integral_le hN htlo hthi)
      (show 0 ≤ ((5 / 2 : Real) * L ^ 2) / |H| by positivity)
    have hx := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ ((5 / 2 : Real) * L ^ 2) * (t / 650) by positivity)
    calc
      _ ≤ ((5 / 2 : Real) * L ^ 2) / |H| * (t / 650) := hi.trans hmaj
      _ = (((5 / 2 : Real) * L ^ 2) * (t / 650)) * (1 / |H|) := by ring
      _ ≤ (((5 / 2 : Real) * L ^ 2) * (t / 650)) *
          (1 / ((99 / 100 : Real) * sourceT N)) := hx
      _ = (5 / 1287 : Real) * (t / sourceT N * L ^ 2) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
      _ ≤ (1 / 250 : Real) * (t / sourceT N * L ^ 2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hscale
      _ = _ := by ring
  change ‖∫ σ in (-(1 : Real) / 2)..(1 + 1 / sourceL N), f σ‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hir]
  calc
    _ ≤ ‖∫ σ in (-(1 : Real) / 2)..(3 / 4 : Real), f σ‖ +
        ‖∫ σ in (3 / 4 : Real)..(1 + 1 / sourceL N), f σ‖ := norm_add_le _ _
    _ ≤ (1 / 5000 : Real) * t / sourceT N * L ^ 2 +
        (1 / 250 : Real) * t / sourceT N * L ^ 2 := add_le_add hleft hright
    _ = _ := by dsimp [L]; ring

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
