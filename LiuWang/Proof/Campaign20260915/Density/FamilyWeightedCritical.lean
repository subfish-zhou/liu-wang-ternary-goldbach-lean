import LiuWang.Proof.Campaign20260915.Density.CriticalKernel

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis (cosineDetector cosineMean)
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_family_weighted_critical_data (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2)) ∧
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      235.69 * ((q : ℝ) * y) ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) *
        Real.log ((q : ℝ) * y) ^ 4 := by
  have hylog := source_height_ge_log_six hy
  obtain ⟨hy', hLy⟩ := source_height_log_bounds hylog
  have hy0 : 0 < y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hLq := Real.log_nonneg hq
  have hLX := Real.log_nonneg (show 1 ≤ (q : ℝ) * y by nlinarith)
  have hd : 0 ≤ sourceDelta y := by unfold sourceDelta; positivity
  have hB (u : ℝ) (hu : 0 ≤ u) : 0 ≤ criticalWindowBudget q y u := by
    unfold criticalWindowBudget
    positivity
  have h := source_family_weighted_window q hylog
    (X := (q : ℝ) * y) (sigma := 1 / 2) ⟨le_rfl, by linarith⟩
    hB (critical_kernel_integrable q y) (fun u hu => source_family_critical_window q hy hu)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  have hbound := h.2.trans (source_critical_kernel_bound q hy)
  have he : ((q : ℝ) * y) ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) =
      q * Real.sqrt q * y ^ 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (mul_pos hq0 hy0), Real.rpow_one,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul hq0.le]
    calc
      _ = (q : ℝ) * Real.sqrt q * y * (Real.sqrt y) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hy0.le]; ring
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ _ := hbound
    _ = _ := by rw [mul_assoc 235.69 _ (y ^ (1 / 2 : ℝ)), he]; ring

theorem source_family_critical_log_four (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖cosineDetector chi ((q : ℝ) * y) y ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      235.69 * ((q : ℝ) * y) ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) *
        Real.log ((q : ℝ) * y) ^ 4 :=
  (source_family_weighted_critical_data q hy).2

theorem source_cosineMean_critical_log_four (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    cosineMean q ((q : ℝ) * y) (1 / 2) y ≤
      (235.69 * ((q : ℝ) * y) ^ (3 / 2 : ℝ) * y ^ (1 / 2 : ℝ) *
        Real.log ((q : ℝ) * y) ^ 4) / q.totient := by
  unfold cosineMean
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  exact div_le_div_of_nonneg_right (source_family_critical_log_four q hy) (Nat.cast_nonneg _)

#print axioms source_family_critical_log_four
#print axioms source_cosineMean_critical_log_four

end LiuWang.Proof.Campaign20260915.Density
