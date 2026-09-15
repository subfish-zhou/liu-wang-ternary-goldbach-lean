import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.MeanContinuity

/-! The finite-mean part of the outer-rectangle limit, without assuming log continuity at zeros. -/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Interval Topology
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def verticalCost (y a U : ℝ) : ℝ :=
  M y a U + 16 * U / (y - 1) ^ 2 + 4 * Real.pi * (1 - a)

def argumentCost (y a U : ℝ) : ℝ := HargIntegral y a U U - HargIntegral y a U (-U)

theorem verticalCost_continuousAt (y : ℝ) {a U : ℝ} (ha : a < 1) :
    ContinuousAt (fun p : ℝ × ℝ => verticalCost y p.1 p.2) (a, U) := by
  unfold verticalCost
  exact ((continuousAt_M_below_one y ha).add
    ((continuousAt_const.mul continuousAt_snd).div_const _)).add
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_fst))

theorem verticalCost_nearby {y a U η : ℝ} (ha : a < 1) (hη : 0 < η) :
    ∃ ε > 0, ∀ b V : ℝ, |b - a| < ε → |V - U| < ε →
      verticalCost y b V < verticalCost y a U + η := by
  have he := (verticalCost_continuousAt y ha).eventually
    (gt_mem_nhds (lt_add_of_pos_right (verticalCost y a U) hη))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε, hε, ?_⟩
  intro b V hb hV
  apply hball (y := (b, V))
  simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro hb hV

theorem H_vertical_cost_le {y a U : ℝ} (hy : 5 ≤ y) (ha : a < 1) (hU : 0 ≤ U) :
    verticalLogIntegral (H y) a U - verticalLogIntegral (H y) 2 U +
        4 * Real.pi * (1 - a) ≤ verticalCost y a U := by
  have hl := log_H_integral_le_M y (ne_of_lt ha) hU
  have hr := abs_log_integral_two_le hy hU
  have hi := intervalIntegrable_log_H_two (by linarith : 3 < y) U
  have hb := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -U ≤ U)
    hi.neg hi.abs (fun t _ => neg_le_abs _)
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hb
  unfold verticalLogIntegral verticalCost
  norm_num only [Complex.ofReal_ofNat]
  linarith

theorem actual_mean_outer_limit {y α d η ε₀ : ℝ} (hy : 10000 ≤ y)
    (hα : α < 1) (hd : 0 < d)
    (hσ : α - d ∈ Icc (1 / 2) (1 - delta y)) (hη : 0 < η) (hε₀ : 0 < ε₀) :
    ∃ a ∈ Ioo (α - d - ε₀) (α - d), ∃ U ∈ Ioo y (y + ε₀),
      (∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) ∧
      2 * Real.pi * d * (zetaDetectorRectangleCount
        ((α : ℂ) - y * I) ((2 : ℂ) + y * I) : ℝ) ≤
        1861 * y ^ (4 * (1 - (α - d))) * Real.log y ^ (6 * (α - d) - 1) +
          16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - d)) + η +
            argumentCost y a U := by
  have hσ1 : α - d < 1 := by linarith
  obtain ⟨ε, hε, hnear⟩ := verticalCost_nearby (y := y) (U := y) hσ1 hη
  let r := min ε ε₀
  have hr : 0 < r := lt_min hε hε₀
  obtain ⟨a, ha, U, hU, hn, _, hc⟩ := actual_H_littlewood_detection
    (by linarith : 3 < y) hα (by linarith : 0 ≤ y) hd hr
  have ha1 : a < 1 := by linarith [ha.2]
  have hU0 : 0 ≤ U := by linarith [hU.1]
  have hab : |a - (α - d)| < ε := by
    apply abs_lt.mpr
    have := min_le_left ε ε₀
    constructor <;> dsimp [r] at ha <;> linarith [ha.1, ha.2]
  have hub : |U - y| < ε := by
    apply abs_lt.mpr
    have := min_le_left ε ε₀
    constructor <;> dsimp [r] at hU <;> linarith [hU.1, hU.2]
  have hnCost := hnear a U hab hub
  have hv := H_vertical_cost_le (by linarith : 5 ≤ y) ha1 hU0
  have hm := M_lemma_3_5_sharp hy hσ
  refine ⟨a, ⟨?_, ha.2⟩, U, ⟨hU.1, ?_⟩, hn, ?_⟩
  · have := min_le_right ε ε₀
    dsimp [r] at ha
    linarith [ha.1]
  · have := min_le_right ε ε₀
    dsimp [r] at hU
    linarith [hU.2]
  · unfold argumentCost verticalCost at *
    linarith

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
