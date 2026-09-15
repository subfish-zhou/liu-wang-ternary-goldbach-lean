import LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.PVMean

/-! Scaling actual finite-window mother bounds while keeping X and M fixed. -/

set_option autoImplicit false
noncomputable section

open Finset
open MathlibNt.SieveTheory.LiuWeight

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis

theorem height_scale {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    1 ≤ 1 + u / y ∧ u ≤ (1 + u / y) * y ∧
      1 + u ≤ (1 + u / y) * (1 + y) := by
  have hd : 0 ≤ u / y := div_nonneg hu hy.le
  have he : u / y * y = u := div_mul_cancel₀ _ hy.ne'
  constructor
  · linarith
  constructor <;> nlinarith

theorem meanFactor_height_le (q K : ℕ) {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    meanFactor q K u ≤ (1 + u / y) * meanFactor q K y := by
  have h := height_scale hy hu
  have hc : 0 ≤ logRowBound q K := by
    unfold logRowBound
    exact mul_nonneg (by positivity) (harmonicRange_nonneg _)
  have hm := mul_le_mul_of_nonneg_right h.1 hc
  unfold meanFactor
  nlinarith only [h.2.1, hm]

theorem mollifier_height_le (q : ℕ) (X : ℝ) {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    mollifierMeanBound q X u ≤ (1 + u / y) * mollifierMeanBound q X y := by
  have h := mul_le_mul_of_nonneg_right (meanFactor_height_le q ⌈X⌉₊ hy hu)
    (harmonicRange_nonneg ⌈X⌉₊)
  exact h.trans_eq (by unfold mollifierMeanBound; ring)

theorem stripError_height_le (q M : ℕ) (sigma : ℝ)
    {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    stripError q M sigma u ≤ (1 + u / y) * stripError q M sigma y := by
  have h := mul_le_mul_of_nonneg_left (height_scale hy hu).2.2
    (by positivity : 0 ≤ 2 * q * (M : ℝ) ^ (-sigma))
  unfold stripError
  nlinarith only [h]

theorem right_mother_height_le (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hX : 1 < X) (hNM : ⌈X⌉₊ ≤ M) (hqN : q ≤ ⌈X⌉₊)
    {sigma y u : ℝ} (hs : 1 ≤ sigma) (hy : 0 < y) (hu : 0 ≤ u) :
    Fmean q X sigma u ≤ (1 + u / y) ^ 3 *
      ((4 * y / ⌈X⌉₊ + 12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1)) *
        liuHarmonic (M * ⌈X⌉₊) ^ 4 +
      2 * stripError q M sigma y ^ 2 * mollifierMeanBound q X y) := by
  let k := 1 + u / y
  have hk : 1 ≤ k := (height_scale hy hu).1
  have hkc : k ≤ k ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hk (by norm_num : 1 ≤ 3)
  have ha : 4 * u / ⌈X⌉₊ +
      12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1) ≤
      k * (4 * y / ⌈X⌉₊ +
        12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1)) := by
    have h1 := mul_le_mul_of_nonneg_left (height_scale hy hu).2.1
      (by positivity : 0 ≤ 4 / (⌈X⌉₊ : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hk
      (mul_nonneg (by positivity : 0 ≤ 12 / (q : ℝ))
        (harmonicRange_nonneg ((M * ⌈X⌉₊ + 1) / q + 1)))
    dsimp [k] at h2 ⊢
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    nlinarith only [h1, h2]
  have hfin := mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ liuHarmonic (M * ⌈X⌉₊) ^ 4)
  have he0 : 0 ≤ stripError q M sigma u := by unfold stripError; positivity
  have he := pow_le_pow_left₀ he0 (stripError_height_le q M sigma hy hu) 2
  have hrem := mul_le_mul he (mollifier_height_le q X hy hu)
    (mollifierMeanBound_nonneg q X hu) (sq_nonneg _)
  have hfin0 : 0 ≤ (4 * y / ⌈X⌉₊ +
      12 / (q : ℝ) * harmonicRange ((M * ⌈X⌉₊ + 1) / q + 1)) *
      liuHarmonic (M * ⌈X⌉₊) ^ 4 :=
    mul_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity) (harmonicRange_nonneg _)))
      (by positivity)
  have hlast := mul_le_mul_of_nonneg_right hkc hfin0
  have hm := Fmean_right_mother q X hX hNM hqN hs hu
  change _ ≤ k ^ 3 * _
  dsimp [k] at hlast ⊢
  nlinarith only [hm, hfin, hrem, hlast]

theorem critical_mother_height_le (q : ℕ) [NeZero q] (X : ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hX : 1 < X) {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    Fmean q X (1 / 2) u ≤ (1 + u / y) ^ 3 *
      (2 * meanFactor q (M * ⌈X⌉₊ + 1) y * liuHarmonic (M * ⌈X⌉₊) ^ 4 +
        8 * prefixBudget q ^ 2 * (1 + y) ^ 2 / M * mollifierMeanBound q X y) := by
  let k := 1 + u / y
  have hk : 1 ≤ k := (height_scale hy hu).1
  have hkc : k ≤ k ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hk (by norm_num : 1 ≤ 3)
  have hfin := mul_le_mul_of_nonneg_right (meanFactor_height_le q (M * ⌈X⌉₊ + 1) hy hu)
    (by positivity : 0 ≤ 2 * liuHarmonic (M * ⌈X⌉₊) ^ 4)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + u) (height_scale hy hu).2.2 2
  have hrem := mul_le_mul hs (mollifier_height_le q X hy hu)
    (mollifierMeanBound_nonneg q X hu) (sq_nonneg _)
  have hrem' := mul_le_mul_of_nonneg_left hrem
    (by positivity : 0 ≤ 8 * prefixBudget q ^ 2 / M)
  have hlast := mul_le_mul_of_nonneg_right hkc
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (meanFactor_nonneg q (M * ⌈X⌉₊ + 1) hy.le))
      (by positivity : 0 ≤ liuHarmonic (M * ⌈X⌉₊) ^ 4))
  have hm := Fmean_critical_PV q X hM hX hu
  change _ ≤ k ^ 3 * _
  dsimp [k] at hlast ⊢
  simp only [div_eq_mul_inv] at hfin hlast hrem' hm ⊢
  nlinarith only [hm, hfin, hrem', hlast]

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis
