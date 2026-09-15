import LiuWang.Proof.Campaign20260915.Density.FamilyRightFinite
import LiuWang.Proof.Campaign20260915.Density.RightMeanLimit

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Filter
open scoped Topology
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters characterPolynomial)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.Campaign20260915.Density

def familyPartial {q : ℕ} (chi : Character q) (X s : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  polynomial chi ((range k).filter (fun n : ℕ => X ≤ (n : ℝ)))
    (rightTerm X s) (fun n => -Real.log n) t

theorem twisted_collected_term {q : ℕ} (chi : Character q) (X s t : ℝ) (n : ℕ) :
    LSeries.term (NonprincipalDensityAdvance.coefficient chi X) ((s : ℂ) + t * I) n =
      chi n * (rightTerm X s n * wave (-Real.log n) t) := by
  rw [← collected_term_wave]
  by_cases hn : n = 0
  · subst n; simp
  · simp only [LSeries.term_of_ne_zero hn, NonprincipalDensityAdvance.coefficient]
    ring

theorem familyPartial_eq_sum {q : ℕ} (chi : Character q) (X s : ℝ) (k : ℕ) (t : ℝ) :
    familyPartial chi X s k t =
      ∑ n ∈ range k,
        LSeries.term (NonprincipalDensityAdvance.coefficient chi X) ((s : ℂ) + t * I) n := by
  unfold familyPartial polynomial characterPolynomial
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : X ≤ (n : ℝ)
  · rw [if_pos hn, twisted_collected_term]
    ring
  · rw [if_neg hn]
    simp [LSeries.term, NonprincipalDensityAdvance.coefficient_eq_zero_of_lt chi
      (lt_of_not_ge hn)]

theorem familyPartial_continuous {q : ℕ} (chi : Character q) (X s : ℝ) (k : ℕ) :
    Continuous (familyPartial chi X s k) :=
  continuous_polynomial chi _ _ _

theorem familyPartial_bound {q : ℕ} (chi : Character q) {X s : ℝ}
    (hX : 1 < X) (hs : 1 < s) (k : ℕ) (t : ℝ) :
    ‖familyPartial chi X s k t‖ ^ 2 ≤ (1 + 1 / (s - 1)) ^ 5 := by
  let S := (range k).filter (fun n : ℕ => X ≤ (n : ℝ))
  have hS (n : ℕ) (hn : n ∈ S) : 0 < n := by
    have : (0 : ℝ) < n := by linarith [(mem_filter.mp hn).2]
    exact_mod_cast this
  have hnorm : ‖familyPartial chi X s k t‖ ≤ ∑ n ∈ S, ‖rightTerm X s n‖ := by
    unfold familyPartial polynomial characterPolynomial
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n _
    rw [norm_mul, norm_mul, norm_wave, mul_one]
    nlinarith [chi.norm_le_one n, norm_nonneg (rightTerm X s n)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (rightTerm_mass_square hS hX hs)

theorem familyPartial_tendsto {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℝ} (hs : 1 < s) (X t : ℝ) :
    Tendsto (fun k => familyPartial chi X s k t) atTop
      (𝓝 (NonprincipalDensityAdvance.f chi X ((s : ℂ) + t * I))) := by
  simp_rw [familyPartial_eq_sum]
  exact (NonprincipalDensityAdvance.f_hasSum chi
    (s := (s : ℂ) + t * I) (by simpa using hs) X).tendsto_sum_nat

theorem actual_family_right_mean {q : ℕ} [NeZero q] {X d T : ℝ}
    (hX : 2 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1) (hT : 0 ≤ T) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -T..T,
      ‖NonprincipalDensityAdvance.f chi X (((1 + d : ℝ) : ℂ) + t * I)‖ ^ 2) / q.totient ≤
      2 * T * ((24 / X) * X ^ (-2 * d)) +
      (4 / q) * (3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4) +
      (8 / q) * X ^ (-d) * (1 + 1 / d) ^ 5 := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX1 : 1 < X := by linarith
  have hs : 1 < 1 + d := by linarith
  let C : ℝ := (nonprincipalCharacters q).card *
    (1 + 1 / ((1 + d) - 1)) ^ 5 / q.totient
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Icc (-T) T))
    (F := fun k t => (∑ chi ∈ nonprincipalCharacters q,
      ‖familyPartial chi X (1 + d) k t‖ ^ 2) / q.totient)
    (f := fun t => (∑ chi ∈ nonprincipalCharacters q,
      ‖NonprincipalDensityAdvance.f chi X (((1 + d : ℝ) : ℂ) + t * I)‖ ^ 2) / q.totient)
    (fun _ => C)
    (fun k => (show Continuous (fun t : ℝ => (∑ chi ∈ nonprincipalCharacters q,
        ‖familyPartial chi X (1 + d) k t‖ ^ 2) / q.totient) by
      exact (continuous_finsetSum _ (fun chi _ =>
        (familyPartial_continuous chi X (1 + d) k).norm.pow 2)).div_const _).aestronglyMeasurable)
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top))
    (fun k => Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have h := sum_le_sum (fun chi (_ : chi ∈ nonprincipalCharacters q) =>
        familyPartial_bound chi hX1 hs k t)
      simpa only [sum_const, nsmul_eq_mul] using h))
    (Eventually.of_forall (fun t =>
      (tendsto_finsetSum _ (fun chi _ => (familyPartial_tendsto chi hs X t).norm.pow 2)).div_const _))
  have hbound (k : ℕ) := family_right_finite_mean hX hd hd1
    (S := (range k).filter (fun n : ℕ => X ≤ (n : ℝ)))
    (fun _ hn => (mem_filter.mp hn).2) hT
  simp only [familyMean_eq_integral] at hbound
  simp only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    ← integral_Icc_eq_integral_Ioc] at hbound
  have hh := le_of_tendsto hlim (Eventually.of_forall hbound)
  have hi (chi : Character q) (hc : chi ∈ nonprincipalCharacters q) :
      IntervalIntegrable (fun t : ℝ =>
        ‖NonprincipalDensityAdvance.f chi X (((1 + d : ℝ) : ℂ) + t * I)‖ ^ 2)
        volume (-T) T := by
    have hc' := (NonprincipalDensityAdvance.mem_nonprincipalCharacters chi).mp hc
    exact (((NonprincipalDensityAdvance.differentiable_f hc' X).continuous.comp
      (by fun_prop)).norm.pow 2).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hh
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum hi] at hh
  exact hh

#print axioms actual_family_right_mean

end LiuWang.Proof.Campaign20260915.Density
