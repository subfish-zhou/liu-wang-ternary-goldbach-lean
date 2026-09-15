import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.SplitIntegral

/-!
# 非对称矩形的两条实际水平边

同一存在量词内提供源半径分离、全线非零性、真实对数导数的有效常数、
可积性及原文 `0.0014` 两边总预算。不声称对称高度选择，也不声称
完整 Perron 或留数公式。
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

theorem exists_source_rectangle_horizontal_estimate
    {N q : Nat} [NeZero q] (hN : Real.exp 2000 ≤ (N : Real))
    (hq : 3 ≤ q) (_hqUpper : (q : Real) ≤ sourceP1 N) {chi : Character q}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {t : Real} (htlo : sourceWindowLower N ≤ t) (hthi : t ≤ (N : Real)) :
    ∃ Hplus Hminus : Real,
      |Hplus - sourceT N| ≤ 1 ∧ |Hminus + sourceT N| ≤ 1 ∧
      (∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
          |(completedZeroValue p).im - Hplus| ∧
        (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
          |(completedZeroValue p).im - Hminus|) ∧
      (∀ H ∈ ({Hplus, Hminus} : Set Real),
        (∀ σ ∈ Set.Icc (-(1 : Real) / 2) (1 + 1 / sourceL N),
          chi.LFunction ((σ : Complex) + (H : Complex) * Complex.I) ≠ 0 ∧
          ‖logDeriv chi.LFunction ((σ : Complex) + (H : Complex) * Complex.I)‖ ≤
            10 * (Real.log ((q : Real) * sourceT N)) ^ 2) ∧
        IntervalIntegrable (fun σ : Real => horizontalIntegrand chi t
          ((σ : Complex) + (H : Complex) * Complex.I))
          volume (-(1 : Real) / 2) (1 + 1 / sourceL N) ∧
        ‖∫ σ in (-(1 : Real) / 2)..(1 + 1 / sourceL N),
          horizontalIntegrand chi t ((σ : Complex) + (H : Complex) * Complex.I)‖ ≤
          (21 / 5000 : Real) * t / sourceT N *
            (Real.log ((q : Real) * sourceT N)) ^ 2) ∧
      (‖∫ σ in (-(1 : Real) / 2)..(1 + 1 / sourceL N),
          horizontalIntegrand chi t ((σ : Complex) + (Hplus : Complex) * Complex.I)‖ +
        ‖∫ σ in (-(1 : Real) / 2)..(1 + 1 / sourceL N),
          horizontalIntegrand chi t ((σ : Complex) + (Hminus : Complex) * Complex.I)‖) /
          (2 * Real.pi) ≤
        0.0014 * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 := by
  obtain ⟨hT, htbig, _, _, hb1, hb2, _⟩ :=
    source_horizontal_parameters hN htlo hthi
  have ht0 : 0 < t := by linarith
  have hT0 := sourceT_pos hN
  have hB := source_height_budget_pos hq hT
  obtain ⟨Hp, Hm, hp, hm, hsep⟩ :=
    exists_source_rectangle_heights_index hq hchi hPrimitive hT
  have hpa : |(|Hp|) - sourceT N| ≤ 1 := by
    have h := (abs_abs_sub_abs_le_abs_sub Hp (sourceT N)).trans hp
    simpa only [abs_of_pos hT0] using h
  have hma : |(|Hm|) - sourceT N| ≤ 1 := by
    have h := abs_abs_sub_abs_le_abs_sub Hm (-sourceT N)
    simp only [abs_neg, abs_of_pos hT0, sub_neg_eq_add] at h
    exact h.trans hm
  have hcommon : ∀ H ∈ ({Hp, Hm} : Set Real),
      |(|H|) - sourceT N| ≤ 1 ∧
      ∀ p : CompletedZeroIndex chi,
        (1.7769 * Real.log ((q : Real) * sourceT N))⁻¹ ≤
          |(completedZeroValue p).im - H| := by
    intro H hH
    rcases Set.mem_insert_iff.mp hH with hh | hh
    · subst H
      exact ⟨hpa, fun p => (hsep p).1⟩
    · have hh' := Set.mem_singleton_iff.mp hh
      subst H
      exact ⟨hma, fun p => (hsep p).2⟩
  refine ⟨Hp, Hm, hp, hm, hsep, ?_, ?_⟩
  · intro H hH
    obtain ⟨ha, hs⟩ := hcommon H hH
    have hH0 : H ≠ 0 := by
      have hh := (source_height_abs_bounds hT ha).1
      intro hz
      norm_num [hz] at hh
    refine ⟨?_, ?_, norm_horizontal_integral_source_sharp_le hN hq hchi hPrimitive htlo hthi ha hs⟩
    · intro σ hσ
      have hslo : -(1 : Real) / 2 ≤ ((σ : Complex) + (H : Complex) * Complex.I).re := by
        simpa using hσ.1
      have hshi : ((σ : Complex) + (H : Complex) * Complex.I).re ≤ 2 := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
          sub_zero, add_zero]
        linarith [hσ.2]
      exact ⟨LFunction_ne_zero_on_separated_strip hchi hPrimitive hB hH0 hs (by simp) hslo,
        norm_logDeriv_source_height_le hq hchi hPrimitive hT ha hs (by simp) hslo hshi⟩
    · exact ContinuousOn.intervalIntegrable_of_Icc (by linarith)
        (continuousOn_horizontalIntegrand hchi hPrimitive ht0 hB hH0 hs)
  · have hpint := norm_horizontal_integral_source_sharp_le hN hq hchi hPrimitive htlo hthi hpa
      (fun p => (hsep p).1)
    have hmint := norm_horizontal_integral_source_sharp_le hN hq hchi hPrimitive htlo hthi hma
      (fun p => (hsep p).2)
    apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
    have hscale : 0 ≤ t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 := by
      positivity
    calc
      _ ≤ (21 / 5000 : Real) * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 +
          (21 / 5000 : Real) * t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2 :=
        add_le_add hpint hmint
      _ = (21 / 2500 : Real) *
          (t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2) := by ring
      _ ≤ (0.0014 * (2 * Real.pi)) *
          (t / sourceT N * (Real.log ((q : Real) * sourceT N)) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hscale
      _ = _ := by ring

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
