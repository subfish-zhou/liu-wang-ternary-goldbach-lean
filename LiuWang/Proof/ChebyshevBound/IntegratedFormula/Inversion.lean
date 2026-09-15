import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Continuity

/-!
# 实际积分 psi 与完整谱原像相等

在固定竖线 Re(s)=3 绝对反演。此处只用实际 Dirichlet 级数的有限范数，
不把存在常数或未知阈值用作原 exp(3100) 域的数值输入。
-/

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory ArithmeticFunction
open LiuWang.Proof.ChebyshevBound.HighHeight
open scoped LSeries.notation

namespace LiuWang.Proof.ChebyshevBound.IntegratedFormula

theorem verticalIntegrable_smoothed_logderiv :
    VerticalIntegrable (fun s => (-deriv riemannZeta s / riemannZeta s) /
      (s * (s + 1))) 3 := by
  let C : ℝ := ∑' n, ‖LSeries.term (↗Λ) (3 : ℂ) n‖
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  have hb (t : ℝ) :
      ‖(-deriv riemannZeta ((3 : ℂ) + (t : ℂ) * I) /
        riemannZeta ((3 : ℂ) + (t : ℂ) * I)) /
        (((3 : ℂ) + (t : ℂ) * I) * ((3 : ℂ) + (t : ℂ) * I + 1))‖ ≤
        C * (1 + t ^ 2)⁻¹ := by
    let s : ℂ := 3 + (t : ℂ) * I
    have hs : 1 < s.re := by dsimp [s]; norm_num
    have hD : ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C := by
      rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
      have h := norm_tsum_le_tsum_norm (LSeriesSummable_vonMangoldt hs).norm
      change ‖LSeries (↗Λ) s‖ ≤ _ at h
      have heq : (fun n => ‖LSeries.term (↗Λ) s n‖) =
          fun n => ‖LSeries.term (↗Λ) (3 : ℂ) n‖ := by
        funext n
        simp [LSeries.norm_term_eq, s]
      rwa [heq] at h
    have hsq : ‖s‖ ^ 2 = 9 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [s, Complex.normSq_apply, pow_two]
    have hsq1 : ‖s + 1‖ ^ 2 = 16 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [s, Complex.normSq_apply, pow_two]
    have hnorm : ‖s‖ ≤ ‖s + 1‖ := by nlinarith [norm_nonneg s, norm_nonneg (s + 1)]
    have hden : 1 + t ^ 2 ≤ ‖s * (s + 1)‖ := by
      rw [norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left hnorm (norm_nonneg s)]
    change ‖(-deriv riemannZeta s / riemannZeta s) / (s * (s + 1))‖ ≤ _
    rw [norm_div]
    calc
      _ ≤ C / ‖s * (s + 1)‖ := div_le_div_of_nonneg_right hD (norm_nonneg _)
      _ ≤ C / (1 + t ^ 2) := div_le_div_of_nonneg_left hC (by positivity) hden
      _ = _ := div_eq_mul_inv _ _
  have hc : Continuous (fun t : ℝ =>
      (-deriv riemannZeta ((3 : ℂ) + (t : ℂ) * I) /
        riemannZeta ((3 : ℂ) + (t : ℂ) * I)) /
        (((3 : ℂ) + (t : ℂ) * I) * ((3 : ℂ) + (t : ℂ) * I + 1))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let s : ℂ := 3 + (t : ℂ) * I
    have hs : 1 < s.re := by dsimp [s]; norm_num
    have hs1 : s ≠ 1 := by intro he; norm_num [he] at hs
    have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
    have hsp : s + 1 ≠ 0 := by
      intro he
      have h := congrArg Complex.re he
      dsimp [s] at h
      norm_num at h
    have ha : AnalyticAt ℂ riemannZeta s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [eventually_ne_nhds hs1] with z hz using differentiableAt_riemannZeta hz
    have hcont := ((ha.deriv.continuousAt.neg.div ha.continuousAt
      (riemannZeta_ne_zero_of_one_lt_re hs)).div
      (continuousAt_id.mul (continuousAt_id.add continuousAt_const)) (mul_ne_zero hs0 hsp))
    have hcurve : ContinuousAt (fun v : ℝ => (3 : ℂ) + (v : ℂ) * I) t := by fun_prop
    have hresult := hcont.comp_of_eq hcurve rfl
    exact hresult
  exact (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem mangoldtSum_eq_spectral {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (∑' n, mangoldtTriangle n u) = spectralMellin u := by
  have hmv : VerticalIntegrable (mellin (fun u => ∑' n, mangoldtTriangle n u)) 3 := by
    apply verticalIntegrable_smoothed_logderiv.congr
    filter_upwards with t
    exact (hasMellin_mangoldtSum (s := ((3 : ℝ) : ℂ) + (t : ℂ) * I) (by norm_num)).2.symm
  have hsv : VerticalIntegrable (mellin spectralMellin) 3 := by
    apply verticalIntegrable_smoothed_logderiv.congr
    filter_upwards with t
    exact (hasMellin_spectralMellin (s := ((3 : ℝ) : ℂ) + (t : ℂ) * I) (by norm_num)).2.symm
  have hm := mellinInv_mellin_eq 3 (fun u => ∑' n, mangoldtTriangle n u) hu
    (hasMellin_mangoldtSum (s := 3) (by norm_num)).1 hmv (continuousAt_mangoldtSum hu hu1)
  have hs := mellinInv_mellin_eq 3 spectralMellin hu
    (hasMellin_spectralMellin (s := 3) (by norm_num)).1 hsv (continuousAt_spectralMellin hu hu1)
  rw [← hm, ← hs]
  unfold mellinInv
  congr 2
  funext t
  rw [mellin_mangoldt_eq_spectral (s := ((3 : ℝ) : ℂ) + (t : ℂ) * I) (by norm_num)]

theorem integratedPsi_eq_spectral {x : ℝ} (hx : 1 < x) :
    (integratedPsi x : ℂ) = (x : ℂ) * spectralMellin x⁻¹ := by
  rw [← mangoldtSum_at_inverse (by linarith : 0 < x),
    mangoldtSum_eq_spectral (inv_pos.mpr (by linarith)) (inv_lt_one_of_one_lt₀ hx)]

end LiuWang.Proof.ChebyshevBound.IntegratedFormula
