import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation.ArgumentBudget

set_option autoImplicit false

noncomputable section

open Complex Set Filter Metric
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Strip

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation

def argumentMajorant (y R a : ℝ) : ℝ :=
  (2 - a) * Real.pi *
    (2 * (Real.log (2 * (1 + windowMajorant y (2 - R)) / (2 - 8 / (y - 1) ^ 2)) /
      Real.log (R / (2 - a))) + 3)

theorem argumentMajorant_continuousAt (y : ℝ) {R a : ℝ}
    (hr : 0 < 2 - a) (hrR : 2 - a < R) :
    ContinuousAt (argumentMajorant y R) a := by
  have hRp : 0 < R := hr.trans hrR
  have hlog : Real.log (R / (2 - a)) ≠ 0 := (Real.log_pos ((one_lt_div hr).mpr hrR)).ne'
  have hc : ContinuousAt (fun x : ℝ => Real.log (R / (2 - x))) a :=
    (continuousAt_const.div (continuousAt_const.sub continuousAt_id) hr.ne').log
      (div_ne_zero hRp.ne' hr.ne')
  exact ((continuousAt_const.sub continuousAt_id).mul_const Real.pi).mul
    ((continuousAt_const.mul (continuousAt_const.div hc hlog)).add continuousAt_const)

theorem zeta_high_alpha_weighted_bound {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    2 * Real.pi * delta y * (zetaDetectorRectangleCount
      ((α : ℂ) - y * I) ((2 : ℂ) + y * I) : ℝ) ≤
      1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
        16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
        argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y) := by
  have hd := delta_bounds hy
  let σ : ℝ := α - delta y
  let R : ℝ := 2 - α + 3 * delta y / 2
  have hσ : σ ∈ Icc (1 / 2) (1 - delta y) := by
    constructor <;> dsimp [σ] <;> linarith [hd.1]
  have hr : 0 < 2 - σ := by dsimp [σ]; linarith [hd.1]
  have hrR : 2 - σ < R := by dsimp [σ, R]; linarith [hd.1]
  apply le_of_forall_pos_le_add
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  have he := (argumentMajorant_continuousAt y hr hrR).eventually
    (gt_mem_nhds (lt_add_of_pos_right (argumentMajorant y R σ) hη2))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he
  let e := min ε (delta y / 4)
  have hepos : 0 < e := lt_min hε (by linarith [hd.1])
  obtain ⟨a, ha, U, hU, hn, hc⟩ := actual_mean_outer_limit hy hα1 hd.1 hσ hη2 hepos
  have heε : e ≤ ε := min_le_left _ _
  have heδ : e ≤ delta y / 4 := min_le_right _ _
  have haa : |a - σ| < ε := by
    apply abs_lt.mpr
    dsimp [σ]
    constructor <;> linarith [ha.1, ha.2]
  have hnear : argumentMajorant y R a < argumentMajorant y R σ + η / 2 := by
    apply hball (y := a)
    simpa only [Real.dist_eq] using haa
  have ha1 : a < 1 := by linarith [ha.2, hd.1]
  have haR : 2 - a < R := by dsimp [R]; linarith [ha.1, hd.1]
  have hRU : R < U := by dsimp [R]; linarith [hU.1, hd.2]
  have hR : R ≤ 3 / 2 := by dsimp [R]; linarith [hd.1]
  have hwin : |U - y| + R ≤ 3 / 2 := by
    rw [abs_of_pos (by linarith [hU.1] : 0 < U - y)]
    dsimp [R]
    linarith [hU.2, hd.1]
  have harg := argumentCost_jensen_bound hy ha1 haR hRU hR hwin hn
  change argumentCost y a U ≤ argumentMajorant y R a at harg
  change _ ≤ _ + argumentMajorant y R σ + η
  linarith

theorem actual_zeta_high_alpha_density {y α : ℝ} (hy : 10000 ≤ y)
    (hα : 1 / 2 + 2 * delta y ≤ α) (hα1 : α < 1) :
    (zetaDetectorRectangleCount ((α : ℂ) - y * I) ((2 : ℂ) + y * I) : ℝ) ≤
      (1861 * y ^ (4 * (1 - (α - delta y))) * Real.log y ^ (6 * (α - delta y) - 1) +
        16 * y / (y - 1) ^ 2 + 4 * Real.pi * (1 - (α - delta y)) +
        argumentMajorant y (2 - α + 3 * delta y / 2) (α - delta y)) /
        (2 * Real.pi * delta y) := by
  have hp : 0 < 2 * Real.pi * delta y := by
    have hd := (delta_bounds hy).1
    positivity
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using zeta_high_alpha_weighted_bound hy hα hα1

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
