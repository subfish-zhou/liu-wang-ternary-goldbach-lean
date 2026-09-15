import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.CubicMoment

/-! Whole-axis exponential means of the actual fixed-X, fixed-modulus family. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

def familyDensity (q : ℕ) [NeZero q] (X sigma t : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q,
    ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

def exponentialMean (q : ℕ) [NeZero q] (X sigma y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
    ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
      Real.exp (-|t| / y)) / q.totient

theorem familyDensity_nonneg (q : ℕ) [NeZero q] (X sigma t : ℝ) :
    0 ≤ familyDensity q X sigma t :=
  div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem continuous_familyDensity (q : ℕ) [NeZero q] (X sigma : ℝ) :
    Continuous (familyDensity q X sigma) := by
  apply Continuous.div_const
  apply continuous_finsetSum
  intro chi hchi
  have h := differentiable_f ((mem_nonprincipalCharacters chi).mp hchi) X
  exact ((h.continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).norm).pow 2

theorem familyDensity_window (q : ℕ) [NeZero q] (X sigma u : ℝ) :
    (∫ t in -u..u, familyDensity q X sigma t) = Fmean q X sigma u := by
  unfold familyDensity Fmean
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
  intro chi hchi
  exact f_vertical_integrable ((mem_nonprincipalCharacters chi).mp hchi) X sigma u

theorem exponential_family_of_windows (q : ℕ) [NeZero q] (X sigma : ℝ)
    {y C : ℝ} (hy : 0 < y)
    (hw : ∀ u : ℝ, 0 ≤ u → Fmean q X sigma u ≤ (1 + u / y) ^ 3 * C) :
    (∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y))) ∧ exponentialMean q X sigma y ≤ 16 * C := by
  have hw' : ∀ u : ℝ, 0 ≤ u →
      (∫ t in -u..u, familyDensity q X sigma t) ≤ (1 + u / y) ^ 3 * C := by
    intro u hu
    rw [familyDensity_window]
    exact hw u hu
  obtain ⟨hi, hb⟩ := exponential_of_cubic_windows (continuous_familyDensity q X sigma)
    (familyDensity_nonneg q X sigma) hy hw'
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hsingle (chi : Character q) (hchi : chi ∈ nonprincipalCharacters q) (t : ℝ) :
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (q.totient : ℝ) * familyDensity q X sigma t := by
    unfold familyDensity
    rw [mul_div_cancel₀ _ hphi.ne']
    exact Finset.single_le_sum (f := fun chi : Character q =>
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2)
      (fun _ _ => sq_nonneg _) hchi
  have his (chi : Character q) (hchi : chi ∈ nonprincipalCharacters q) :
      Integrable (fun t : ℝ =>
        ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
          Real.exp (-|t| / y)) := by
    apply (hi.const_mul (q.totient : ℝ)).mono'
    · have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * Complex.I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hc := ((differentiable_f ((mem_nonprincipalCharacters chi).mp hchi) X).continuous.comp hv).norm.pow 2
      exact (hc.mul (Real.continuous_exp.comp (continuous_id.abs.neg.div_const y))).aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hsingle chi hchi t)
        (Real.exp_pos _).le
  refine ⟨his, ?_⟩
  have he : (∫ t : ℝ, familyDensity q X sigma t * Real.exp (-|t| / y)) =
      exponentialMean q X sigma y := by
    unfold familyDensity exponentialMean
    simp_rw [div_mul_eq_mul_div, sum_mul]
    rw [integral_div, integral_finsetSum _ his]
  rwa [he] at hb

theorem exponential_right_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : 1 ≤ sigma) :
    (∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y))) ∧
      exponentialMean q ((q : ℝ) * y) sigma y ≤
        288768 * (1 + Real.log ((q : ℝ) * y)) ^ 5 / q := by
  have h := exponential_family_of_windows q ((q : ℝ) * y) sigma
    (by linarith) (fun _ hu => Fmean_right_fixed_X q hy hs hu)
  exact ⟨h.1, h.2.trans_eq (by unfold rightBudget; ring)⟩

theorem exponential_critical_fixed_X (q : ℕ) [NeZero q] {y : ℝ}
    (hy : 2 ≤ y) {M : ℕ} (hM : 2 ≤ M) :
    (∀ chi ∈ nonprincipalCharacters q, Integrable (fun t : ℝ =>
      ‖NonprincipalDensityAdvance.f chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y))) ∧
      exponentialMean q ((q : ℝ) * y) (1 / 2) y ≤
        16 * criticalBudget q ((q : ℝ) * y) M y := by
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    exponential_family_of_windows q ((q : ℝ) * y) (1 / 2)
      (by linarith) (fun _ hu => Fmean_critical_fixed_X q hy hu hM)

theorem exponentialMean_unnormalized (q : ℕ) [NeZero q] (X sigma y C : ℝ)
    (h : exponentialMean q X sigma y ≤ C) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t : ℝ,
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2 *
        Real.exp (-|t| / y)) ≤ (q.totient : ℝ) * C := by
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact ((div_le_iff₀ hphi).mp h).trans_eq (mul_comm _ _)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
