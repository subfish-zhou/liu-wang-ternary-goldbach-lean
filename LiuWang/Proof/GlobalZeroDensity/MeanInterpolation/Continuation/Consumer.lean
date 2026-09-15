import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.PerturbedMean

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory
open scoped Interval
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

theorem actual_high_alpha_detector {y α η ε : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) (hη : 0 < η) (hε : 0 < ε) :
    ∃ a ∈ Ioo (α - delta y - ε) (α - delta y), ∃ U ∈ Ioo y (y + ε),
      (∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), entireH y s ≠ 0) ∧
      (∀ h ∈ ({-U, U} : Set ℝ),
        ContinuousOn (HhorizontalLog y 2 U h) [[a, 2]] ∧
        IntervalIntegrable (fun x : ℝ => (HhorizontalLog y 2 U h x).im) volume a 2 ∧
        ∀ x ∈ [[a, 2]], Complex.exp (HhorizontalLog y 2 U h x) = H y ((x : ℂ) + h * I)) ∧
      2 * Real.pi * delta y * (zetaDetectorRectangleCount
        ((α : ℂ) - y * I) ((2 : ℂ) + y * I) : ℝ) ≤
        1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
          16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) + η +
            argumentCost y a U := by
  have hd := (delta_bounds hy).1
  have hσ : α - delta y ∈ Icc (1 / 2) (1 - delta y) := by constructor <;> linarith
  obtain ⟨a, ha, U, hU, hn, hc⟩ := actual_mean_outer_limit hy hα1 hd hσ hη hε
  have ha1 : a < 1 := by linarith [ha.2]
  have hU0 : 0 < U := by linarith [hU.1]
  refine ⟨a, ha, U, hU, hn, ?_, hc⟩
  intro h hh
  have hh' : h = -U ∨ h = U := by simpa using hh
  exact ⟨HhorizontalLog_continuousOn ha1 hU0 hn hh',
    (HargIntegral_split ha1 hU0 hn hh').1,
    fun x hx => HhorizontalLog_exp ha1 hU0 hn hh' hx⟩

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
