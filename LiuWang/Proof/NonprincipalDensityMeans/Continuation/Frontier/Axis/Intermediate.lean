import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.FamilyHolder

/-! Direct intermediate-line weighted energies and actual means, without assuming L2 interpolation. -/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Classical
open MathlibNt.SieveTheory.LiuWeight
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

theorem weighted_tail_strip_energy (q : ℕ) [NeZero q] {M N : ℕ}
    (hN : 2 ≤ N) (hNM : N ≤ M) {sigma : ℝ} (hs : sigma ∈ Set.Icc (1 / 2) 1) :
    unitEnergy q (tailSupport M N) (verticalCoefficient (detectorCoefficient M N) sigma) ≤
        (N : ℝ) ^ (1 - 2 * sigma) * liuHarmonic (M * N) ^ 4 ∧
    firstUnitEnergy q (tailSupport M N) (verticalCoefficient (detectorCoefficient M N) sigma) ≤
        (M * N : ℕ) ^ (2 - 2 * sigma) * liuHarmonic (M * N) ^ 4 := by
  have hsub : tailSupport M N ⊆ (range (M * N + 1)).erase 0 := filter_subset _ _
  have hcrit : (∑ n ∈ tailSupport M N,
      ‖verticalCoefficient (detectorCoefficient M N) (1 / 2) n‖ ^ 2) ≤ liuHarmonic (M * N) ^ 4 :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      (detectorCoefficient_critical_energy (hN.trans hNM) hN)
  constructor
  · exact (unitEnergy_le q _ _).trans
      ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
        (detectorCoefficient_strip_energy hN hNM hs.1))
  · apply (firstUnitEnergy_le q _ _).trans
    have hp : (∑ n ∈ tailSupport M N,
        (n : ℝ) * ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2) ≤
        (M * N : ℕ) ^ (2 - 2 * sigma) *
          ∑ n ∈ tailSupport M N, ‖verticalCoefficient (detectorCoefficient M N) (1 / 2) n‖ ^ 2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := Nat.pos_of_ne_zero (mem_erase.mp (hsub hn)).1
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
      have hnK : (n : ℝ) ≤ (M * N : ℕ) :=
        Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp (mem_erase.mp (hsub hn)).2))
      have he : (n : ℝ) * ‖verticalCoefficient (detectorCoefficient M N) sigma n‖ ^ 2 =
          ‖verticalCoefficient (detectorCoefficient M N) (1 / 2) n‖ ^ 2 *
            (n : ℝ) ^ (2 - 2 * sigma) := by
        rw [critical_weight_shift hn0, critical_weight_shift hn0]
        norm_num only [show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, Real.rpow_zero, mul_one]
        rw [show 2 - 2 * sigma = 1 + (1 - 2 * sigma) by ring,
          Real.rpow_add hnR, Real.rpow_one]
        ring
      rw [he]
      exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hnR.le hnK (by linarith [hs.2]))
        (sq_nonneg _)).trans_eq (mul_comm _ _)
    exact hp.trans (mul_le_mul_of_nonneg_left hcrit (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem finiteDetector_intermediate_mean (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma u : ℝ} (hs : sigma ∈ Set.Icc (1 / 2) 1) (hu : 0 ≤ u) :
    (∑ chi ∈ nonprincipalCharacters q, ∫ t in -u..u,
      ‖finiteDetector chi X M ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient ≤
      (2 * u * (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) +
        6 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1) *
          (M * ⌈X⌉₊ : ℕ) ^ (2 - 2 * sigma)) * liuHarmonic (M * ⌈X⌉₊) ^ 4 := by
  have hN : 2 ≤ ⌈X⌉₊ := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have he := weighted_tail_strip_energy q hN hNM hs
  have h := weighted_dirichlet_mean q (S := tailSupport M ⌈X⌉₊) (K := M * ⌈X⌉₊ + 1)
    (filter_subset _ _) (fun _ hn => hqN.trans (mem_filter.mp hn).2)
    (detectorCoefficient M ⌈X⌉₊) sigma hu
  have hb := (h.trans (sub_le_self _ (div_nonneg
    (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)))).trans
      (add_le_add (mul_le_mul_of_nonneg_left he.1 (by positivity : 0 ≤ 2 * u))
        (mul_le_mul_of_nonneg_left he.2 (mul_nonneg (by positivity) (harmonicRange_nonneg _))))
  simp_rw [finiteDetector_eq_tail _ X hX hNM]
  exact hb.trans_eq (by ring)

def intermediateBudget (q : ℕ) (X : ℝ) (M : ℕ) (sigma y : ℝ) : ℝ :=
  (4 * y * (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) +
    12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1) *
      (M * ⌈X⌉₊ : ℕ) ^ (2 - 2 * sigma)) * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
    2 * stripError q M sigma y ^ 2 * mollifierMeanBound q X y

theorem Fmean_intermediate_mother (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma u : ℝ} (hs : sigma ∈ Set.Icc (1 / 2) 1) (hu : 0 ≤ u) :
    Fmean q X sigma u ≤ intermediateBudget q X M sigma u := by
  have hM : 2 ≤ M := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have hf := mul_le_mul_of_nonneg_left (finiteDetector_intermediate_mean q X hX hNM hqN hs hu)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hQ := mul_le_mul_of_nonneg_left (Qmean_strip_le q X hs.1 hu)
    (by positivity : 0 ≤ 2 * stripError q M sigma u ^ 2)
  exact (Fmean_strip_le_finite_and_Q q X hM hX hs.1 hu).trans
    ((add_le_add hf hQ).trans_eq (by unfold intermediateBudget; ring))

theorem intermediate_height_le (q : ℕ) (X : ℝ) (M : ℕ) (sigma : ℝ)
    {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    intermediateBudget q X M sigma u ≤ (1 + u / y) ^ 3 * intermediateBudget q X M sigma y := by
  let a := 4 * (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) * liuHarmonic (M * ⌈X⌉₊) ^ 4
  let b := 12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1) *
    (M * ⌈X⌉₊ : ℕ) ^ (2 - 2 * sigma) * liuHarmonic (M * ⌈X⌉₊) ^ 4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (harmonicRange_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
  have hk := (height_scale hy hu).1
  have hkc : 1 + u / y ≤ (1 + u / y) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hk (by norm_num : 1 ≤ 3)
  have h1 := mul_le_mul_of_nonneg_left (height_scale hy hu).2.1 ha
  have h2 := mul_le_mul_of_nonneg_right hk hb
  have h3 := mul_le_mul_of_nonneg_right hkc (add_nonneg (mul_nonneg ha hy.le) hb)
  have he := pow_le_pow_left₀ (by unfold stripError; positivity : 0 ≤ stripError q M sigma u)
    (stripError_height_le q M sigma hy hu) 2
  have hrem := mul_le_mul he (mollifier_height_le q X hy hu)
    (mollifierMeanBound_nonneg q X hu) (sq_nonneg _)
  unfold intermediateBudget
  dsimp [a, b] at h1 h2 h3
  nlinarith only [h1, h2, h3, hrem]

theorem exponential_intermediate_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    exponentialMean q ((q : ℝ) * y) sigma y ≤
      16 * intermediateBudget q ((q : ℝ) * y) M sigma y := by
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  exact (exponential_family_of_windows q ((q : ℝ) * y) sigma (by linarith) (fun u hu =>
    (Fmean_intermediate_mother q ((q : ℝ) * y) (by nlinarith) hNM hp.2.1 hs hu).trans
      (intermediate_height_le q _ M sigma (by linarith) hu))).2

theorem cosine_intermediate_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    cosineMean q ((q : ℝ) * y) sigma y ≤
      256 * intermediateBudget q ((q : ℝ) * y) M sigma y := by
  have h := cosineMean_le_exponential q ((q : ℝ) * y) hy
    (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩) (fun chi hchi =>
      exponential_strip_integrable ((mem_nonprincipalCharacters chi).mp hchi) _ (by linarith) hs.1)
  exact h.trans ((mul_le_mul_of_nonneg_left (exponential_intermediate_fixed_X q hy hs hNM)
    (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

theorem Fmean_intermediate_axis_consumer (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    Fmean q ((q : ℝ) * y) sigma y ≤
      768 * intermediateBudget q ((q : ℝ) * y) M sigma y :=
  (Fmean_le_cosineMean q _ hy hs).trans ((mul_le_mul_of_nonneg_left
    (cosine_intermediate_fixed_X q hy hs hNM) (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
