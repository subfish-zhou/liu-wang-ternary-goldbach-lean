import LiuWang.Proof.Campaign20260915.Density.L2Boundary

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology
open Complex.HadamardThreeLines

namespace LiuWang.Proof.Campaign20260915.Density.L2Strip

theorem squareWindow_interpolation {f : ℂ → ℂ} {lo hi a b sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi)) (hab : a < b)
    (hinside : verticalClosedStrip a b ⊆ verticalStrip lo hi)
    (hbdd : BddAbove ((norm ∘ f) '' verticalClosedStrip a b))
    (hints : ∀ s ∈ Icc a b, Integrable (fun t : ℝ => ‖f ((s : ℂ) + t * I)‖ ^ 2))
    (hs : sigma ∈ Icc a b) (T : ℝ) :
    squareWindow f sigma T ≤
      squareMean f a ^ (1 - (sigma - a) / (b - a)) * squareMean f b ^ ((sigma - a) / (b - a)) := by
  have hW := squareWindow_nonneg f sigma T
  have hleft := squareMean_nonneg f a
  have hright := squareMean_nonneg f b
  have hbound : BddAbove ((norm ∘ (fun z => correlation f sigma T z ^ 2)) ''
      verticalClosedStrip a b) := by
    obtain ⟨B, hB⟩ := correlation_bounded hbdd hs T
    refine ⟨(max B 0) ^ 2, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Function.comp_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)) 2
  have hdiff : DiffContOnCl ℂ (fun z => correlation f sigma T z ^ 2) (verticalStrip a b) :=
    ⟨(correlation_diffContOnCl hf hab hinside hs T).1.pow 2,
      (correlation_diffContOnCl hf hab hinside hs T).2.pow 2⟩
  have hs' : (sigma : ℂ) ∈ verticalStrip lo hi :=
    hinside (by simpa only [verticalClosedStrip, mem_preimage, ofReal_re] using hs)
  have hL : ∀ z ∈ Complex.re ⁻¹' {a},
      ‖correlation f sigma T z ^ 2‖ ≤ squareMean f a * squareWindow f sigma T := by
    intro z hz
    have he : z.re = a := hz
    have hz' : z.re ∈ Icc a b := by rw [he]; exact ⟨le_rfl, hab.le⟩
    simpa only [he] using correlation_sq_bound hf hs' T (hinside hz') (hints z.re hz')
  have hR : ∀ z ∈ Complex.re ⁻¹' {b},
      ‖correlation f sigma T z ^ 2‖ ≤ squareMean f b * squareWindow f sigma T := by
    intro z hz
    have he : z.re = b := hz
    have hz' : z.re ∈ Icc a b := by rw [he]; exact ⟨hab.le, le_rfl⟩
    simpa only [he] using correlation_sq_bound hf hs' T (hinside hz') (hints z.re hz')
  have h := norm_le_interp_of_mem_verticalClosedStrip' hab
    (show (sigma : ℂ) ∈ verticalClosedStrip a b by simpa [verticalClosedStrip] using hs)
    hdiff hbound hL hR
  rw [norm_pow, correlation_self, Complex.norm_real, Real.norm_of_nonneg hW] at h
  simp only [Complex.ofReal_re] at h
  by_cases hz : squareWindow f sigma T = 0
  · rw [hz]
    exact mul_nonneg (Real.rpow_nonneg hleft _) (Real.rpow_nonneg hright _)
  have hp : 0 < squareWindow f sigma T := lt_of_le_of_ne hW (Ne.symm hz)
  rw [Real.mul_rpow hleft hW, Real.mul_rpow hright hW] at h
  have hprod : squareWindow f sigma T ^ (1 - (sigma - a) / (b - a)) *
      squareWindow f sigma T ^ ((sigma - a) / (b - a)) = squareWindow f sigma T := by
    rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
  have he : squareMean f a ^ (1 - (sigma - a) / (b - a)) *
        squareWindow f sigma T ^ (1 - (sigma - a) / (b - a)) *
        (squareMean f b ^ ((sigma - a) / (b - a)) *
          squareWindow f sigma T ^ ((sigma - a) / (b - a))) =
      (squareMean f a ^ (1 - (sigma - a) / (b - a)) *
        squareMean f b ^ ((sigma - a) / (b - a))) * squareWindow f sigma T := by
    calc
      _ = (squareMean f a ^ (1 - (sigma - a) / (b - a)) *
        squareMean f b ^ ((sigma - a) / (b - a))) *
          (squareWindow f sigma T ^ (1 - (sigma - a) / (b - a)) *
            squareWindow f sigma T ^ ((sigma - a) / (b - a))) := by ring
      _ = _ := by rw [hprod]
  rw [he, pow_two] at h
  exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [h])

theorem squareWindow_tendsto {f : ℂ → ℂ} {sigma : ℝ}
    (hi : Integrable (fun t : ℝ => ‖f ((sigma : ℂ) + t * I)‖ ^ 2)) :
    Tendsto (fun n : ℕ => squareWindow f sigma n) atTop (𝓝 (squareMean f sigma)) := by
  have hcover : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge |t|
    exact mem_iUnion.mpr ⟨n, abs_le.mp hn⟩
  have hmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := by
    intro m n hmn
    have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact Icc_subset_Icc (neg_le_neg h) h
  have hi' : IntegrableOn (fun t : ℝ => ‖f ((sigma : ℂ) + t * I)‖ ^ 2)
      (⋃ n : ℕ, Icc (-(n : ℝ)) n) := by
    rw [hcover, integrableOn_univ]
    exact hi
  have h := tendsto_setIntegral_of_monotone (fun n : ℕ =>
    measurableSet_Icc (a := -(n : ℝ)) (b := n)) hmono hi'
  rw [hcover, setIntegral_univ] at h
  exact h

theorem squareMean_interpolation {f : ℂ → ℂ} {lo hi a b sigma : ℝ}
    (hf : AnalyticOnNhd ℂ f (verticalStrip lo hi)) (hab : a < b)
    (hinside : verticalClosedStrip a b ⊆ verticalStrip lo hi)
    (hbdd : BddAbove ((norm ∘ f) '' verticalClosedStrip a b))
    (hints : ∀ s ∈ Icc a b, Integrable (fun t : ℝ => ‖f ((s : ℂ) + t * I)‖ ^ 2))
    (hs : sigma ∈ Icc a b) :
    squareMean f sigma ≤
      squareMean f a ^ (1 - (sigma - a) / (b - a)) * squareMean f b ^ ((sigma - a) / (b - a)) :=
  le_of_tendsto (squareWindow_tendsto (hints sigma hs))
    (Eventually.of_forall (fun n : ℕ => squareWindow_interpolation hf hab hinside hbdd hints hs n))

#print axioms squareMean_interpolation

end LiuWang.Proof.Campaign20260915.Density.L2Strip
