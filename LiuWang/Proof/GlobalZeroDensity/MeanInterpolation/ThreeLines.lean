import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Boundary

/-! Genuine L2 three-lines interpolation, first for finite windows and then on the full axis. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity.Strip
open Complex.HadamardThreeLines

namespace LiuWang.Proof.GlobalZeroDensity.MeanInterpolation

theorem weightedMean_nonneg (y σ : ℝ) : 0 ≤ weightedMean y σ :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem correlation_sq_bound {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (T : ℝ) {z : ℂ}
    (hz : z.re ∈ Icc (1 / 2) (1 + delta y)) :
    ‖correlation y σ T z ^ 2‖ ≤ weightedMean y z.re * squareWindow y σ T := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (correlation_cauchy_schwarz hy hσ T hz) 2
  rw [mul_pow, Real.sq_sqrt (weightedMean_nonneg _ _),
    Real.sq_sqrt (squareWindow_nonneg _ _ _), ← norm_pow] at h
  exact h

theorem squareWindow_interpolation {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (T : ℝ) :
    squareWindow y σ T ≤
      (weightedMean y (1 / 2)) ^ (1 - rightWeight y σ) *
        (weightedMean y (1 + delta y)) ^ rightWeight y σ := by
  have hd := delta_bounds hy
  have hW := squareWindow_nonneg y σ T
  have hleft := weightedMean_nonneg y (1 / 2)
  have hright := weightedMean_nonneg y (1 + delta y)
  have hbound : BddAbove ((norm ∘ (fun z => correlation y σ T z ^ 2)) ''
      verticalClosedStrip (1 / 2) (1 + delta y)) := by
    obtain ⟨B, hB⟩ := correlation_bounded hy hσ T
    refine ⟨(max B 0) ^ 2, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.comp_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)) 2
  have hdiff : DiffContOnCl ℂ (fun z => correlation y σ T z ^ 2)
      (verticalStrip (1 / 2) (1 + delta y)) :=
    ⟨(correlation_diffContOnCl hy hσ T).1.pow 2,
      (correlation_diffContOnCl hy hσ T).2.pow 2⟩
  have hL : ∀ z ∈ Complex.re ⁻¹' {(1 / 2 : ℝ)},
      ‖correlation y σ T z ^ 2‖ ≤ weightedMean y (1 / 2) * squareWindow y σ T := by
    intro z hz
    have he : z.re = 1 / 2 := hz
    have hz' : z.re ∈ Icc (1 / 2) (1 + delta y) := by rw [he]; constructor <;> linarith
    simpa only [he] using correlation_sq_bound hy hσ T hz'
  have hR : ∀ z ∈ Complex.re ⁻¹' {1 + delta y},
      ‖correlation y σ T z ^ 2‖ ≤ weightedMean y (1 + delta y) * squareWindow y σ T := by
    intro z hz
    have he : z.re = 1 + delta y := hz
    have hz' : z.re ∈ Icc (1 / 2) (1 + delta y) := by rw [he]; constructor <;> linarith
    simpa only [he] using correlation_sq_bound hy hσ T hz'
  have hi := norm_le_interp_of_mem_verticalClosedStrip'
    (by linarith : (1 / 2 : ℝ) < 1 + delta y)
    (show (σ : ℂ) ∈ verticalClosedStrip (1 / 2) (1 + delta y) by
      simpa [verticalClosedStrip] using hσ) hdiff hbound hL hR
  rw [norm_pow, correlation_self, Complex.norm_real, Real.norm_of_nonneg hW] at hi
  simp only [Complex.ofReal_re] at hi
  rw [show 1 + delta y - 1 / 2 = 1 / 2 + delta y by ring] at hi
  change squareWindow y σ T ^ 2 ≤
    (weightedMean y (1 / 2) * squareWindow y σ T) ^ (1 - rightWeight y σ) *
      (weightedMean y (1 + delta y) * squareWindow y σ T) ^ rightWeight y σ at hi
  by_cases hzero : squareWindow y σ T = 0
  · rw [hzero]
    exact mul_nonneg (Real.rpow_nonneg hleft _) (Real.rpow_nonneg hright _)
  have hpos : 0 < squareWindow y σ T := lt_of_le_of_ne hW (Ne.symm hzero)
  rw [Real.mul_rpow hleft hW, Real.mul_rpow hright hW] at hi
  have hprod : squareWindow y σ T ^ (1 - rightWeight y σ) *
      squareWindow y σ T ^ rightWeight y σ = squareWindow y σ T := by
    rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
  have heq :
      weightedMean y (1 / 2) ^ (1 - rightWeight y σ) *
        squareWindow y σ T ^ (1 - rightWeight y σ) *
        (weightedMean y (1 + delta y) ^ rightWeight y σ *
          squareWindow y σ T ^ rightWeight y σ) =
      (weightedMean y (1 / 2) ^ (1 - rightWeight y σ) *
        weightedMean y (1 + delta y) ^ rightWeight y σ) * squareWindow y σ T := by
    calc
      _ = (weightedMean y (1 / 2) ^ (1 - rightWeight y σ) *
        weightedMean y (1 + delta y) ^ rightWeight y σ) *
        (squareWindow y σ T ^ (1 - rightWeight y σ) *
          squareWindow y σ T ^ rightWeight y σ) := by ring
      _ = _ := by rw [hprod]
  rw [heq, pow_two] at hi
  exact (mul_le_mul_iff_left₀ hpos).mp (by nlinarith [hi])

theorem squareWindow_tendsto {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    Tendsto (fun n : ℕ => squareWindow y σ n) atTop (𝓝 (weightedMean y σ)) := by
  have hcover : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge |t|
    exact mem_iUnion.mpr ⟨n, by have := abs_le.mp hn; exact this⟩
  have hmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := by
    intro m n hmn
    have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact Icc_subset_Icc (neg_le_neg h) h
  have hi : IntegrableOn (fun t : ℝ => ‖regularG y ((σ : ℂ) + t * I)‖ ^ 2)
      (⋃ n : ℕ, Icc (-(n : ℝ)) n) := by
    rw [hcover, integrableOn_univ]
    exact regularG_strip_integrable hy hσ
  have h := tendsto_setIntegral_of_monotone (fun n : ℕ =>
    measurableSet_Icc (a := -(n : ℝ)) (b := n)) hmono hi
  rw [hcover, setIntegral_univ] at h
  exact h

theorem weightedMean_interpolation {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    weightedMean y σ ≤
      (weightedMean y (1 / 2)) ^ (1 - rightWeight y σ) *
        (weightedMean y (1 + delta y)) ^ rightWeight y σ :=
  le_of_tendsto (squareWindow_tendsto hy hσ)
    (Eventually.of_forall (fun n : ℕ => squareWindow_interpolation hy hσ n))

end LiuWang.Proof.GlobalZeroDensity.MeanInterpolation
