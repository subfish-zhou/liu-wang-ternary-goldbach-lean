import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Intermediate

/-! Actual all-sigma PV remainders, with strict partial sums and summable mean-square errors. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Filter Classical
open scoped Topology
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

theorem LFunction_Abel_PV {q M : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖chi.LFunction s - partialL chi M s‖ ≤
      prefixBudget q * (1 + ‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  have h := DirichletCharacter.norm_LFunction_sub_sum_le_of_prefix_bound chi hchi s hs
    (prefixBudget q) (nonprincipal_prefix_budget q chi hchi) hM
  rw [← partialL_eq_Abel_sum hchi] at h
  exact h.trans_eq (by ring)

theorem partialL_vertical_continuous {q : ℕ} (chi : Character q) (M : ℕ) (sigma : ℝ) :
    Continuous (fun t : ℝ => partialL chi M ((sigma : ℂ) + t * Complex.I)) := by
  unfold partialL
  simp_rw [dirichletPolynomial_eq_wave chi ((range M).erase 0)
    (fun _ hn => Nat.pos_of_ne_zero (mem_erase.mp hn).1) (fun _ => 1) sigma]
  exact continuous_polynomial _ _ _ _

theorem remainder_vertical_continuous {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) (M : ℕ) (sigma : ℝ) :
    Continuous (fun t : ℝ =>
      NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I) -
        finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)) := by
  have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  simp_rw [f_sub_finiteDetector]
  exact (((DirichletCharacter.differentiable_LFunction hchi).continuous.comp hv).sub
    (partialL_vertical_continuous chi M sigma)).mul ((differentiable_Q chi X).continuous.comp hv)

def remainderMean (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (sigma u : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -u..u,
    ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I) -
      finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

theorem remainderMean_nonneg (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (sigma : ℝ)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ remainderMean q X M sigma u :=
  div_nonneg (sum_nonneg fun _ _ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem remainderMean_critical (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (u : ℝ) :
    remainderMean q X M (1 / 2) u = FremainderMean q X M u := by
  simp only [remainderMean, FremainderMean, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

theorem remainderMean_le_PV (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hM : 1 ≤ M) {sigma u : ℝ} (hs : 1 / 2 ≤ sigma) (hu : 0 ≤ u) :
    remainderMean q X M sigma u ≤ pvError q M sigma u ^ 2 * Qmean q X sigma u := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -u..u,
        ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I) -
          finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        pvError q M sigma u ^ 2 *
          (∫ t in -u..u, ‖NonprincipalDensityAdvance.Q chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hR := ((remainder_vertical_continuous hchi X M sigma).norm.pow 2).intervalIntegrable
      (μ := volume) (-u) u
    have hQ := Q_vertical_integrable chi X sigma u
    have h := intervalIntegral.integral_mono_on (by linarith : -u ≤ u) hR
      (hQ.const_mul (pvError q M sigma u ^ 2)) (fun t ht => by
        simp only [Pi.pow_apply]
        rw [f_sub_finiteDetector, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (LFunction_truncation_PV hchi hM hs (abs_le.mpr ht)) 2)
          (sq_nonneg _))
    rwa [intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [← mul_sum] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq (by unfold Qmean; ring)

theorem pvError_sq (q M : ℕ) (sigma u : ℝ) :
    pvError q M sigma u ^ 2 =
      4 * prefixBudget q ^ 2 * (1 + u) ^ 2 * (M : ℝ) ^ (-2 * sigma) := by
  unfold pvError
  rw [mul_pow, mul_pow, mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (-sigma)) 2,
    ← Real.rpow_mul (Nat.cast_nonneg M)]
  norm_num only [Nat.cast_ofNat]
  rw [show (-sigma) * (2 : ℝ) = -2 * sigma by ring]

theorem remainderMean_le_reciprocal (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hM : 1 ≤ M) {sigma u : ℝ} (hs : 1 / 2 ≤ sigma) (hu : 0 ≤ u) :
    remainderMean q X M sigma u ≤
      (4 * prefixBudget q ^ 2 * (1 + u) ^ 2 * mollifierMeanBound q X u) / M := by
  have hp : (M : ℝ) ^ (-2 * sigma) ≤ (M : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr hM) (show -2 * sigma ≤ -1 by linarith)
  have h := (remainderMean_le_PV q X hM hs hu).trans
    (mul_le_mul_of_nonneg_left (Qmean_strip_le q X hs hu) (sq_nonneg _))
  rw [pvError_sq] at h
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by positivity : 0 ≤ 4 * prefixBudget q ^ 2 * (1 + u) ^ 2)
      (mollifierMeanBound_nonneg q X hu))
  exact h.trans (by
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm)

theorem remainderMean_dyadic (q : ℕ) [NeZero q] (X : ℝ)
    {sigma u : ℝ} (hs : 1 / 2 ≤ sigma) (hu : 0 ≤ u) :
    Summable (fun k : ℕ => remainderMean q X (2 ^ k) sigma u) ∧
      (∑' k : ℕ, remainderMean q X (2 ^ k) sigma u) ≤
        8 * prefixBudget q ^ 2 * (1 + u) ^ 2 * mollifierMeanBound q X u := by
  have h := dyadic_summable_of_reciprocal_bound (fun M => remainderMean q X M sigma u)
    (4 * prefixBudget q ^ 2 * (1 + u) ^ 2 * mollifierMeanBound q X u)
    (fun M => remainderMean_nonneg q X M sigma hu)
    (fun _ hM => remainderMean_le_reciprocal q X hM hs hu)
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

theorem remainderMean_dyadic_tendsto_zero (q : ℕ) [NeZero q] (X : ℝ)
    {sigma u : ℝ} (hs : 1 / 2 ≤ sigma) (hu : 0 ≤ u) :
    Tendsto (fun k : ℕ => remainderMean q X (2 ^ k) sigma u) atTop (𝓝 0) :=
  (remainderMean_dyadic q X hs hu).1.tendsto_atTop_zero

theorem Fmean_le_finite_and_PV (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hX : 1 < X) {sigma u : ℝ} (hs : 1 / 2 ≤ sigma) (hu : 0 ≤ u) :
    Fmean q X sigma u ≤
      2 * ((∑ chi ∈ nonprincipalCharacters q, ∫ t in -u..u,
        ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient) +
      2 * pvError q M sigma u ^ 2 * Qmean q X sigma u := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -u..u, ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) ≤
        2 * (∫ t in -u..u, ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) +
        2 * (∫ t in -u..u,
          ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I) -
            finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) := by
    have hP := finiteDetector_strip_integrable chi X hM hX sigma u
    have hR := ((remainder_vertical_continuous hchi X M sigma).norm.pow 2).intervalIntegrable
      (μ := volume) (-u) u
    have h := intervalIntegral.integral_mono_on (by linarith : -u ≤ u)
      (f_vertical_integrable hchi X sigma u) ((hP.const_mul 2).add (hR.const_mul 2))
      (fun t _ => by
        simpa only [add_sub_cancel, Pi.pow_apply] using
          norm_add_sq_le (finiteDetector chi X M ((sigma : ℂ) + t * Complex.I))
            (NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I) -
              finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)))
    rwa [intervalIntegral.integral_add (hP.const_mul 2) (hR.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h
  have h' := div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)
  have hR := mul_le_mul_of_nonneg_left (remainderMean_le_PV q X (by omega : 1 ≤ M) hs hu)
    (by norm_num : (0 : ℝ) ≤ 2)
  unfold Fmean remainderMean at *
  simp only [div_eq_mul_inv] at h' hR ⊢
  nlinarith only [h', hR]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation
