import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.WeightedMean

/-! # Apply index-weighted means to the actual cancelled detector coefficients -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

def tailSupport (M N : ℕ) : Finset ℕ :=
  ((range (M * N + 1)).erase 0).filter (fun n => N ≤ n)

theorem finiteDetector_eq_tail {q : ℕ} (chi : Character q) (X : ℝ)
    {M : ℕ} (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (s : ℂ) :
    finiteDetector chi X M s =
      dirichletPolynomial chi (tailSupport M ⌈X⌉₊) (detectorCoefficient M ⌈X⌉₊) s := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  rw [finiteDetector_eq_collected chi X (hN.trans hNM) hX]
  symm
  apply sum_subset (filter_subset _ _)
  intro n hn hn'
  have hnN : n < ⌈X⌉₊ := by
    simpa only [tailSupport, mem_filter, hn, true_and, not_le] using hn'
  rw [detectorCoefficient_eq_zero_below
    (Nat.pos_of_ne_zero (mem_erase.mp hn).1) (hnN.trans_le hNM) hnN, zero_mul, zero_div]

theorem weighted_coefficient_le_divisors {M N n : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hn : 0 < n) {sigma : ℝ} (hs : 1 ≤ sigma) :
    (n : ℝ) * ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2 ≤
      (n.divisors.card : ℝ) ^ 2 * (n : ℝ)⁻¹ := by
  rw [critical_weight_shift hn]
  have hp : (n : ℝ) ^ (1 - 2 * sigma) ≤ (n : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr hn) (show 1 - 2 * sigma ≤ -1 by linarith)
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have he : (n : ℝ) * (‖detectorCoefficient M N n‖ ^ 2 * (n : ℝ)⁻¹ *
      (n : ℝ) ^ (1 - 2 * sigma)) =
        ‖detectorCoefficient M N n‖ ^ 2 * (n : ℝ) ^ (1 - 2 * sigma) := by
    field_simp
  rw [he]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (detectorCoefficient_norm_le hM hN n) 2)
    hp (by positivity) (sq_nonneg _)

theorem detector_tail_energies (q : ℕ) [NeZero q] {M N : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) {sigma : ℝ} (hs : 1 ≤ sigma) :
    unitEnergy q (tailSupport M N) (verticalCoefficient (detectorCoefficient M N) sigma) ≤
        (N : ℝ)⁻¹ * liuHarmonic (M * N) ^ 4 ∧
    firstUnitEnergy q (tailSupport M N) (verticalCoefficient (detectorCoefficient M N) sigma) ≤
        liuHarmonic (M * N) ^ 4 := by
  have hsum : (∑ n ∈ tailSupport M N,
      (n : ℝ) * ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2) ≤
        liuHarmonic (M * N) ^ 4 := by
    apply le_trans (sum_le_sum (fun n hn => weighted_coefficient_le_divisors (hN.trans hNM) hN
      (Nat.pos_of_ne_zero (mem_erase.mp (mem_filter.mp hn).1).1) hs))
    apply le_trans _ (AnalyticNumberTheory.LargeSieve.divisorSquareWeightedPrefix_le_fourth_harmonic _)
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hn' := mem_erase.mp (mem_filter.mp hn).1
      exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn'.1, Nat.le_of_lt_succ (mem_range.mp hn'.2)⟩
    · intro _ _ _
      positivity
  refine ⟨?_, (firstUnitEnergy_le q _ _).trans hsum⟩
  have hpoint : (∑ n ∈ tailSupport M N,
      ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2) ≤
      (N : ℝ)⁻¹ * ∑ n ∈ tailSupport M N,
        (n : ℝ) * ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr (mem_filter.mp hn).2
    have h := mul_le_mul_of_nonneg_right hNn
      (sq_nonneg ‖verticalCoefficient (detectorCoefficient M N) sigma n‖)
    have hb := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hNr.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hNr.ne', one_mul] using hb
  exact (unitEnergy_le q _ _).trans
    (hpoint.trans (mul_le_mul_of_nonneg_left hsum (by positivity)))

theorem finiteDetector_right_mean (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma y : ℝ} (hs : 1 ≤ sigma) (hy : 0 ≤ y) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
      ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient ≤
      (2 * y / ⌈X⌉₊ + 6 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1)) *
        liuHarmonic (M * ⌈X⌉₊) ^ 4 := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have h := weighted_dirichlet_mean q (S := tailSupport M ⌈X⌉₊) (K := M * ⌈X⌉₊ + 1)
    (filter_subset _ _)
    (fun n hn => hqN.trans (mem_filter.mp hn).2) (detectorCoefficient M ⌈X⌉₊) sigma hy
  have he := detector_tail_energies q hN hNM hs
  have hb := (h.trans (sub_le_self _ (div_nonneg
    (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _))
    (Nat.cast_nonneg _)))).trans (add_le_add
      (mul_le_mul_of_nonneg_left he.1 (by positivity : 0 ≤ 2 * y))
      (mul_le_mul_of_nonneg_left he.2 (mul_nonneg (by positivity) (harmonicRange_nonneg _))))
  simp_rw [finiteDetector_eq_tail _ X hX hNM]
  exact hb.trans_eq (by ring)

theorem Fmean_right_mother (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma y : ℝ} (hs : 1 ≤ sigma) (hy : 0 ≤ y) :
    Fmean q X sigma y ≤
      (4 * y / ⌈X⌉₊ + 12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1)) *
        liuHarmonic (M * ⌈X⌉₊) ^ 4 +
      2 * stripError q M sigma y ^ 2 * mollifierMeanBound q X y := by
  have hM : 2 ≤ M := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have h := add_le_add
    (mul_le_mul_of_nonneg_left (finiteDetector_right_mean q X hX hNM hqN hs hy)
      (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (Qmean_strip_le q X (sigma := sigma) (by linarith) hy)
      (by positivity : 0 ≤ 2 * stripError q M sigma y ^ 2))
  exact (Fmean_strip_le_finite_and_Q q X hM hX (by linarith) hy).trans (h.trans_eq (by ring))

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
