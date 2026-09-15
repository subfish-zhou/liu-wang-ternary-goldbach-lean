import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.Continuation.AbelMean

/-! Replace only the actual Abel remainder; preserve the indexed finite energy and all endpoints. -/

set_option autoImplicit false
noncomputable section

open Finset
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

def pvBudget (q : ℕ) (X : ℝ) (M : ℕ) (sigma u : ℝ) : ℝ :=
  (4 * u * (⌈X⌉₊ : ℝ) ^ (1 - 2 * sigma) +
    12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1) *
      (M * ⌈X⌉₊ : ℕ) ^ (2 - 2 * sigma)) * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
    2 * pvError q M sigma u ^ 2 * mollifierMeanBound q X u

theorem pvBudget_nonneg (q : ℕ) (X : ℝ) (M : ℕ) (sigma : ℝ)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pvBudget q X M sigma u := by
  unfold pvBudget
  exact add_nonneg
    (mul_nonneg (add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by positivity) (harmonicRange_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (by positivity))
    (mul_nonneg (by positivity) (mollifierMeanBound_nonneg q X hu))

theorem pvBudget_le_old (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (sigma : ℝ)
    {u : ℝ} (hu : 0 ≤ u) : pvBudget q X M sigma u ≤ intermediateBudget q X M sigma u := by
  have h0 : 0 ≤ pvError q M sigma u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (prefixBudget_nonneg q)) (by positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (pvError_le_stripError q M sigma hu) 2)
      (by norm_num : (0 : ℝ) ≤ 2)) (mollifierMeanBound_nonneg q X hu)
  exact add_le_add le_rfl h

theorem pvBudget_saving (q : ℕ) (X : ℝ) (M : ℕ) (sigma u : ℝ) :
    intermediateBudget q X M sigma u - pvBudget q X M sigma u =
      8 * ((q : ℝ) ^ 2 - prefixBudget q ^ 2) * (1 + u) ^ 2 *
        (M : ℝ) ^ (-2 * sigma) * mollifierMeanBound q X u := by
  unfold intermediateBudget pvBudget
  rw [stripError_sq, pvError_sq]
  ring

theorem Fmean_PV_mother (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma u : ℝ} (hs : sigma ∈ Set.Icc (1 / 2) 1) (hu : 0 ≤ u) :
    Fmean q X sigma u ≤ pvBudget q X M sigma u := by
  have hM : 2 ≤ M := by
    have : 1 < ⌈X⌉₊ := Nat.lt_ceil.mpr (by simpa using hX)
    omega
  have hf := mul_le_mul_of_nonneg_left (finiteDetector_intermediate_mean q X hX hNM hqN hs hu)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hQ := mul_le_mul_of_nonneg_left (Qmean_strip_le q X hs.1 hu)
    (by positivity : 0 ≤ 2 * pvError q M sigma u ^ 2)
  exact (Fmean_le_finite_and_PV q X hM hX hs.1 hu).trans
    ((add_le_add hf hQ).trans_eq (by unfold pvBudget; ring))

theorem pvError_height_le (q : ℕ) [NeZero q] (M : ℕ) (sigma : ℝ)
    {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    pvError q M sigma u ≤ (1 + u / y) * pvError q M sigma y := by
  have hP := prefixBudget_nonneg q
  have h := mul_le_mul_of_nonneg_left (height_scale hy hu).2.2
    (by positivity : 0 ≤ 2 * prefixBudget q * (M : ℝ) ^ (-sigma))
  unfold pvError
  nlinarith only [h]

theorem pvBudget_height_le (q : ℕ) [NeZero q] (X : ℝ) (M : ℕ) (sigma : ℝ)
    {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    pvBudget q X M sigma u ≤ (1 + u / y) ^ 3 * pvBudget q X M sigma y := by
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
  have he0 : 0 ≤ pvError q M sigma u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (prefixBudget_nonneg q)) (by positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have he := pow_le_pow_left₀ he0 (pvError_height_le q M sigma hy hu) 2
  have hrem := mul_le_mul he (mollifier_height_le q X hy hu)
    (mollifierMeanBound_nonneg q X hu) (sq_nonneg _)
  unfold pvBudget
  dsimp [a, b] at h1 h2 h3
  nlinarith only [h1, h2, h3, hrem]

theorem Fmean_PV_fixed_X (q : ℕ) [NeZero q] {y sigma : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    Fmean q ((q : ℝ) * y) sigma y ≤ pvBudget q ((q : ℝ) * y) M sigma y := by
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  exact Fmean_PV_mother q _ (by nlinarith) hNM hp.2.1 hs (by linarith)

theorem Fmean_PV_all_heights (q : ℕ) [NeZero q] {y sigma u : ℝ}
    (hy : 2 ≤ y) (hs : sigma ∈ Set.Icc (1 / 2) 1) (hu : 0 ≤ u)
    {M : ℕ} (hNM : ⌈(q : ℝ) * y⌉₊ ≤ M) :
    Fmean q ((q : ℝ) * y) sigma u ≤ (1 + u / y) ^ 3 * pvBudget q ((q : ℝ) * y) M sigma y := by
  have hp := ceil_parameters q hy
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  exact (Fmean_PV_mother q _ (by nlinarith) hNM hp.2.1 hs hu).trans
    (pvBudget_height_le q _ M sigma (by linarith) hu)

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation
