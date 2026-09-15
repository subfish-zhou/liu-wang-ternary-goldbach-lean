import LiuWang.Proof.Campaign20260915.Density.RightFiniteMean

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Filter Set
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.Campaign20260915.Density

def collectedPartial (y s : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ range k, LSeries.term (coefficient y) ((s : ℂ) + t * I) n

theorem collected_term_wave (y s t : ℝ) (n : ℕ) :
    LSeries.term (coefficient y) ((s : ℂ) + t * I) n =
      rightTerm y s n * wave (-Real.log n) t := by
  by_cases hn : n = 0
  · subst n; simp [rightTerm]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, rightTerm, LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ hn0]
  have he : ((n : ℂ) ^ ((t : ℂ) * I))⁻¹ = wave (-Real.log n) t := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_neg]
    unfold wave
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  simp only [div_eq_mul_inv, mul_inv_rev, he]
  ring

theorem collectedPartial_eq_polynomial (y s : ℝ) (k : ℕ) (t : ℝ) :
    collectedPartial y s k t =
      exponentialPolynomial ((range k).erase 0) (rightTerm y s) (fun n => -Real.log n) t := by
  unfold collectedPartial exponentialPolynomial
  rw [← sum_subset (erase_subset 0 (range k)) (fun n hn hnot => by
    have he : n = 0 := by
      by_contra hne
      exact hnot (mem_erase.mpr ⟨hne, hn⟩)
    subst n
    simp)]
  exact sum_congr rfl (fun n _ => collected_term_wave y s t n)

theorem collectedPartial_continuous (y s : ℝ) (k : ℕ) :
    Continuous (collectedPartial y s k) := by
  simp_rw [funext (collectedPartial_eq_polynomial y s k)]
  unfold exponentialPolynomial wave
  fun_prop

theorem collectedPartial_bound {y s : ℝ} (hy : 1 < y) (hs : 1 < s)
    (k : ℕ) (t : ℝ) :
    ‖collectedPartial y s k t‖ ^ 2 ≤ (1 + 1 / (s - 1)) ^ 5 := by
  rw [collectedPartial_eq_polynomial]
  have hnorm : ‖exponentialPolynomial ((range k).erase 0) (rightTerm y s)
      (fun n => -Real.log n) t‖ ≤ ∑ n ∈ (range k).erase 0, ‖rightTerm y s n‖ := by
    unfold exponentialPolynomial
    have h := norm_sum_le ((range k).erase 0)
      (fun n => rightTerm y s n * wave (-Real.log n) t)
    simpa only [norm_mul, norm_wave, mul_one] using h
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (rightTerm_mass_square (fun n hn => Nat.pos_of_ne_zero (mem_erase.mp hn).1) hy hs)

theorem collectedPartial_tendsto {s : ℝ} (hs : 1 < s) (y t : ℝ) :
    Tendsto (fun k => collectedPartial y s k t) atTop
      (𝓝 (f y ((s : ℂ) + t * I))) :=
  (f_hasSum (y := y) (s := (s : ℂ) + t * I) (by simpa using hs)).tendsto_sum_nat

theorem actual_right_mean {y d T : ℝ} (hy : 1 < y) (hd : 0 < d) (hT : 0 ≤ T) :
    M y (1 + d) T ≤
      2 * T * ((24 / y) * y ^ (-2 * d)) +
      4 * (3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4) +
      4 * (1 + 1 / d) ^ 5 := by
  have hs : 1 < 1 + d := by linarith
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Icc (-T) T))
    (F := fun k t => ‖collectedPartial y (1 + d) k t‖ ^ 2)
    (f := fun t => F y (((1 + d : ℝ) : ℂ) + t * I))
    (fun _ => (1 + 1 / ((1 + d) - 1)) ^ 5)
    (fun k => ((collectedPartial_continuous y (1 + d) k).norm.pow 2).aestronglyMeasurable)
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top))
    (fun k => Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact collectedPartial_bound hy hs k t))
    (Eventually.of_forall (fun t => (collectedPartial_tendsto hs y t).norm.pow 2))
  have hbound (k : ℕ) :
      (∫ t in -T..T, ‖collectedPartial y (1 + d) k t‖ ^ 2) ≤
      2 * T * ((24 / y) * y ^ (-2 * d)) +
      4 * (3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4) +
      4 * (1 + 1 / d) ^ 5 := by
    simp_rw [collectedPartial_eq_polynomial]
    exact right_finite_mean
      (fun n hn => Nat.pos_of_ne_zero (mem_erase.mp hn).1) hy hd hT
  simp only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    ← integral_Icc_eq_integral_Ioc] at hbound
  have h := le_of_tendsto hlim (Eventually.of_forall hbound)
  rw [GlobalZeroDensity.M, intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    ← integral_Icc_eq_integral_Ioc]
  exact h

#print axioms actual_right_mean

end LiuWang.Proof.Campaign20260915.Density
