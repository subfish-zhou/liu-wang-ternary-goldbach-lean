import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.PoleCorrection

/-! Littlewood for the original H, with the pole factor's exact correction. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def verticalLogIntegral (f : ℂ → ℂ) (σ U : ℝ) : ℝ :=
  ∫ t in -U..U, Real.log ‖f ((σ : ℂ) + t * I)‖

def horizontalArgIntegral (f : ℂ → ℂ) (a U h : ℝ) : ℝ :=
  ∫ x in a..2, (horizontalLog f 2 U h x).im

def HargIntegral (y a U h : ℝ) : ℝ := ∫ x in a..2, (HhorizontalLog y 2 U h x).im

theorem HhorizontalLog_continuousOn {y a U h : ℝ} (ha : a < 1) (hU : 0 < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0)
    (hh : h = -U ∨ h = U) :
    ContinuousOn (HhorizontalLog y 2 U h) [[a, 2]] := by
  have he := rectangle_nonzero_lines (a := a) (b := 2) (c := -U) (d := U)
    (f := entireH y) (by simpa [sub_eq_add_neg] using hn)
  have hp := rectangle_nonzero_lines (a := a) (b := 2) (c := -U) (d := U)
    (f := poleFactor) (by simpa [sub_eq_add_neg] using poleFactor_boundary ha hU)
  have hnE : ∀ x ∈ [[a, 2]], lineValue (entireH y) (h * I) 1 x ≠ 0 := by
    have hx := hh.elim (fun e => e ▸ he.1) (fun e => e ▸ he.2.1)
    simpa [lineValue, add_comm] using hx
  have hnP : ∀ x ∈ [[a, 2]], lineValue poleFactor (h * I) 1 x ≠ 0 := by
    have hx := hh.elim (fun e => e ▸ hp.1) (fun e => e ▸ hp.2.1)
    simpa [lineValue, add_comm] using hx
  exact (lineLog_continuousOn (differentiable_entireH y) hnE).sub
    (continuousOn_const.mul (lineLog_continuousOn poleFactor_differentiable hnP))

theorem vertical_log_split {y σ U : ℝ} (hσ : σ ≠ 1)
    (hn : ∀ t ∈ [[-U, U]], entireH y ((σ : ℂ) + t * I) ≠ 0) :
    verticalLogIntegral (entireH y) σ U =
      verticalLogIntegral (H y) σ U + 2 * verticalLogIntegral poleFactor σ U := by
  have hs : ∀ t : ℝ, (σ : ℂ) + t * I ≠ 1 := by
    intro t he
    have := congrArg Complex.re he
    simp at this
    exact hσ this
  have hp : Continuous (fun t : ℝ => Real.log ‖poleFactor ((σ : ℂ) + t * I)‖) :=
    (show Continuous (fun t : ℝ => poleFactor ((σ : ℂ) + t * I)) by
      unfold poleFactor; fun_prop).norm.log (fun t => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hs t)))
  have hiH := log_H_vertical_integrable y hσ U
  have hiP := hp.intervalIntegrable (μ := volume) (-U) U
  unfold verticalLogIntegral
  rw [intervalIntegral.integral_congr (fun t ht => log_entireH_split (hs t) (hn t ht)),
    intervalIntegral.integral_add hiH (hiP.const_mul 2), intervalIntegral.integral_const_mul]

theorem HargIntegral_split {y a U h : ℝ} (ha : a < 1) (hU : 0 < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0)
    (hh : h = -U ∨ h = U) :
    IntervalIntegrable (fun x : ℝ => (HhorizontalLog y 2 U h x).im) volume a 2 ∧
    HargIntegral y a U h = horizontalArgIntegral (entireH y) a U h -
      2 * horizontalArgIntegral poleFactor a U h := by
  have he := rectangle_logs_integrable (differentiable_entireH y) (a := a) (b := 2)
    (c := -U) (d := U) (by simpa [sub_eq_add_neg] using hn)
  have hp := rectangle_logs_integrable poleFactor_differentiable (a := a) (b := 2)
    (c := -U) (d := U) (by simpa [sub_eq_add_neg] using poleFactor_boundary ha hU)
  have hiE : IntervalIntegrable (horizontalLog (entireH y) 2 U h) volume a 2 :=
    hh.elim (fun e => e ▸ he.1) (fun e => e ▸ he.2.1)
  have hiP : IntervalIntegrable (horizontalLog poleFactor 2 U h) volume a 2 :=
    hh.elim (fun e => e ▸ hp.1) (fun e => e ▸ hp.2.1)
  have heq : (fun x : ℝ => (HhorizontalLog y 2 U h x).im) =
      (fun x : ℝ => (horizontalLog (entireH y) 2 U h x).im -
        2 * (horizontalLog poleFactor 2 U h x).im) := by
    funext x
    simp [HhorizontalLog, mul_im]
  have hie : IntervalIntegrable (fun x : ℝ => (horizontalLog (entireH y) 2 U h x).im) volume a 2 :=
    ⟨hiE.1.im, hiE.2.im⟩
  have hip : IntervalIntegrable (fun x : ℝ => (horizontalLog poleFactor 2 U h x).im) volume a 2 :=
    ⟨hiP.1.im, hiP.2.im⟩
  refine ⟨by rw [heq]; exact hie.sub (hip.const_mul 2), ?_⟩
  unfold HargIntegral horizontalArgIntegral
  rw [heq, intervalIntegral.integral_sub hie (hip.const_mul 2), intervalIntegral.integral_const_mul]

theorem original_H_littlewood {y a U : ℝ} (ha : a < 1) (hU : 0 < U)
    (hn : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) :
    2 * Real.pi *
      (RectangleIntegral' (weightedDetectorKernel y ((a : ℂ) - U * I))
        ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re =
      verticalLogIntegral (H y) a U - verticalLogIntegral (H y) 2 U +
        HargIntegral y a U U - HargIntegral y a U (-U) + 4 * Real.pi * (1 - a) := by
  have he := rectangle_littlewood_entire (differentiable_entireH y) (a := a) (b := 2)
    (c := -U) (d := U) (by simpa [sub_eq_add_neg] using hn)
  simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg, ofReal_ofNat] at he
  change 2 * Real.pi *
    (RectangleIntegral' (weightedDetectorKernel y ((a : ℂ) - U * I))
      ((a : ℂ) - U * I) ((2 : ℂ) + U * I)).re =
    verticalLogIntegral (entireH y) a U - verticalLogIntegral (entireH y) 2 U +
      horizontalArgIntegral (entireH y) a U U - horizontalArgIntegral (entireH y) a U (-U) at he
  have hn' : ∀ s ∈ RectangleBorder ((a : ℂ) + (-U : ℝ) * I) ((2 : ℂ) + U * I), entireH y s ≠ 0 := by
    simpa [sub_eq_add_neg] using hn
  obtain ⟨_, _, hnA, hnB⟩ := rectangle_nonzero_lines hn'
  have hvA := vertical_log_split (ne_of_lt ha) hnA
  have hvB := vertical_log_split (by norm_num : (2 : ℝ) ≠ 1) hnB
  have ht := (HargIntegral_split ha hU hn (Or.inr rfl)).2
  have hb := (HargIntegral_split ha hU hn (Or.inl rfl)).2
  have hp := poleFactor_littlewood ha hU
  change 2 * Real.pi * (1 - a) = verticalLogIntegral poleFactor a U -
    verticalLogIntegral poleFactor 2 U + horizontalArgIntegral poleFactor a U U -
      horizontalArgIntegral poleFactor a U (-U) at hp
  rw [hvA, hvB] at he
  linarith

theorem actual_H_littlewood_detection {y α T d ε : ℝ} (hy : 3 < y)
    (hα : α < 1) (hT : 0 ≤ T) (hd : 0 < d) (hε : 0 < ε) :
    ∃ a ∈ Ioo (α - d - ε) (α - d), ∃ U ∈ Ioo T (T + ε),
      (∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) ∧
      (∀ h ∈ ({-U, U} : Set ℝ), ∀ x ∈ [[a, 2]],
        Complex.exp (HhorizontalLog y 2 U h x) = H y ((x : ℂ) + h * I)) ∧
      2 * Real.pi * d * (zetaDetectorRectangleCount
        ((α : ℂ) - T * I) ((2 : ℂ) + T * I) : ℝ) ≤
        verticalLogIntegral (H y) a U - verticalLogIntegral (H y) 2 U +
          HargIntegral y a U U - HargIntegral y a U (-U) + 4 * Real.pi * (1 - a) := by
  obtain ⟨a, ha, U, hU, hn, _, hc⟩ :=
    closed_zeta_weighted_detection hy (by linarith) hT hd hε (α := α)
  have ha1 : a < 1 := by linarith [ha.2]
  have hU0 : 0 < U := by linarith [hU.1]
  refine ⟨a, ha, U, hU, hn, ?_, ?_⟩
  · intro h hh x hx
    exact HhorizontalLog_exp ha1 hU0 hn (by simpa using hh) hx
  · have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * Real.pi)
    rw [original_H_littlewood ha1 hU0 hn] at hh
    nlinarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
