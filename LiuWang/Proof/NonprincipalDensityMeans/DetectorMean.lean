import LiuWang.Proof.NonprincipalDensityMeans.CriticalValue

/-!
# Paid vertical means of the actual detector L(s,chi) Q(chi,X,s) - 1

Two independent critical estimates retain the fixed-level Q/L mean savings.
The moving-right estimate uses the genuine Mobius-inverse tail.
These estimates do not assert the final high-alpha density inequality.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

def Fmean (q : ℕ) [NeZero q] (X sigma y : ℝ) : ℝ :=
  (∑ chi ∈ nonprincipalCharacters q, ∫ t in -y..y,
    ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) / q.totient

theorem f_vertical_integrable {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X sigma y : ℝ) :
    IntervalIntegrable (fun t =>
      ‖NonprincipalDensityAdvance.f chi X ((sigma : ℂ) + t * Complex.I)‖ ^ 2) volume (-y) y := by
  have hv : Continuous (fun t : ℝ => (sigma : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact ((((differentiable_f hchi X).continuous.comp hv).norm).pow 2).intervalIntegrable _ _

theorem Fmean_nonneg (q : ℕ) [NeZero q] (X sigma : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ Fmean q X sigma y := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun chi _ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

theorem f_norm_sq_le {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    ‖NonprincipalDensityAdvance.f chi X s‖ ^ 2 ≤
      2 * ‖chi.LFunction s‖ ^ 2 * ‖NonprincipalDensityAdvance.Q chi X s‖ ^ 2 + 2 := by
  have h := norm_add_sq_le (chi.LFunction s * NonprincipalDensityAdvance.Q chi X s) (-1)
  simpa only [NonprincipalDensityAdvance.f, sub_eq_add_neg, norm_mul, norm_neg,
    norm_one, one_pow, mul_pow, mul_assoc, mul_one] using h

theorem Q_critical_norm_sq_le {q : ℕ} (chi : Character q) (X t : ℝ) :
    ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      4 * (⌈X⌉₊ : ℝ) := by
  rw [Q_critical_eq_wave]
  have hn : ‖polynomial chi ((range ⌈X⌉₊).erase 0) criticalCoefficient
      (fun n => -Real.log n) t‖ ≤ 2 * Real.sqrt ⌈X⌉₊ := by
    calc
      _ ≤ ∑ n ∈ (range ⌈X⌉₊).erase 0,
          ‖criticalCoefficient n * wave (-Real.log n) t * chi n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (range ⌈X⌉₊).erase 0, (Real.sqrt n)⁻¹ := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul, norm_mul, norm_wave, mul_one]
        exact (mul_le_of_le_one_right (norm_nonneg _) (chi.norm_le_one n)).trans
          (norm_criticalCoefficient_le (Nat.pos_of_ne_zero (mem_erase.mp hn).1))
      _ ≤ ∑ n ∈ range ⌈X⌉₊, (Real.sqrt n)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ ≤ _ := GlobalZeroDensity.sum_inv_sqrt_le ⌈X⌉₊
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg ⌈X⌉₊),
    show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem Fmean_critical_le_Qmean (q : ℕ) [NeZero q] (X : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      64 * q * (1 + y) * Qmean q X (1 / 2) y + 4 * y * nonprincipalRatio q := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        64 * q * (1 + y) *
          (∫ t in -y..y, ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) +
            4 * y := by
    have hQ := Q_vertical_integrable chi X (1 / 2) y
    have hf := f_vertical_integrable hchi X (1 / 2) y
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hQ hf
    have hR := (hQ.const_mul (64 * q * (1 + y))).add
      (intervalIntegrable_const (c := (2 : ℝ)))
    have hi := intervalIntegral.integral_mono_on (by linarith : -y ≤ y) hf hR
      (fun t ht => by
        have hL := LFunction_critical_norm_sq_le hchi (abs_le.mpr ht)
        have hb := mul_le_mul_of_nonneg_right hL
          (sq_nonneg ‖NonprincipalDensityAdvance.Q chi X ((1 / 2 : ℂ) + t * Complex.I)‖)
        have h := f_norm_sq_le chi X ((1 / 2 : ℂ) + t * Complex.I)
        nlinarith only [h, hb])
    rw [intervalIntegral.integral_add (hQ.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul] at hi
    convert hi using 1
    ring
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  have hb := div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)
  unfold Fmean Qmean nonprincipalRatio
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  calc
    _ ≤ _ := hb
    _ = _ := by ring

theorem Fmean_critical_le_Lmean (q : ℕ) [NeZero q] (X : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      8 * (⌈X⌉₊ : ℝ) * Lmean q (1 / 2) y + 4 * y * nonprincipalRatio q := by
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        8 * (⌈X⌉₊ : ℝ) *
          (∫ t in -y..y, ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) +
            4 * y := by
    have hL := LFunction_vertical_integrable hchi (1 / 2) y
    have hf := f_vertical_integrable hchi X (1 / 2) y
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hL hf
    have hR := (hL.const_mul (8 * (⌈X⌉₊ : ℝ))).add
      (intervalIntegrable_const (c := (2 : ℝ)))
    have hi := intervalIntegral.integral_mono_on (by linarith : -y ≤ y) hf hR
      (fun t _ => by
        have hQ := Q_critical_norm_sq_le chi X t
        have hb := mul_le_mul_of_nonneg_left hQ
          (sq_nonneg ‖chi.LFunction ((1 / 2 : ℂ) + t * Complex.I)‖)
        have h := f_norm_sq_le chi X ((1 / 2 : ℂ) + t * Complex.I)
        nlinarith only [h, hb])
    rw [intervalIntegral.integral_add (hL.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul] at hi
    convert hi using 1
    ring
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  have hb := div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)
  unfold Fmean Lmean nonprincipalRatio
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  calc
    _ ≤ _ := hb
    _ = _ := by ring

theorem Fmean_critical_bound (q : ℕ) [NeZero q] (X : ℝ)
    {M : ℕ} (hM : 1 ≤ M) {y : ℝ} (hy : 0 ≤ y) :
    Fmean q X (1 / 2) y ≤
      min (64 * q * (1 + y) * mollifierMeanBound q X y)
        (8 * (⌈X⌉₊ : ℝ) * LMeanBound q M y) + 4 * y * nonprincipalRatio q := by
  have hQ := (Fmean_critical_le_Qmean q X hy).trans
    (add_le_add (mul_le_mul_of_nonneg_left (Qmean_critical_le q X hy)
      (by positivity : 0 ≤ 64 * (q : ℝ) * (1 + y))) le_rfl)
  have hL := (Fmean_critical_le_Lmean q X hy).trans
    (add_le_add (mul_le_mul_of_nonneg_left (Lmean_critical_le q hM hy)
      (by positivity : 0 ≤ 8 * (⌈X⌉₊ : ℝ))) le_rfl)
  rw [← min_add_add_right]
  exact le_min hQ hL

theorem Fmean_moving_right (q : ℕ) [NeZero q] {X delta y : ℝ}
    (hX : 1 < X) (hd : 0 < delta) (hy : 0 ≤ y) :
    Fmean q X (1 + delta) y ≤
      2 * y * nonprincipalRatio q *
        ((1 + 1 / delta) * (((⌈X⌉₊ : ℝ) - 1) ^ (-delta) / delta)) ^ 2 := by
  let B : ℝ := (1 + 1 / delta) * (((⌈X⌉₊ : ℝ) - 1) ^ (-delta) / delta)
  have hi (chi : Character q) (hchi : chi ≠ 1) :
      (∫ t in -y..y, ‖NonprincipalDensityAdvance.f chi X
        (((1 + delta : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ≤ 2 * y * B ^ 2 := by
    have hpoint (t : ℝ) :
        ‖NonprincipalDensityAdvance.f chi X (((1 + delta : ℝ) : ℂ) + t * Complex.I)‖ ≤ B := by
      have hr : (((1 + delta : ℝ) : ℂ) + t * Complex.I).re = 1 + delta := by simp
      have h := norm_f_le_right chi (s := ((1 + delta : ℝ) : ℂ) + t * Complex.I)
        (by rw [hr]; linarith) hX
      simpa only [hr, add_sub_cancel_left, show 1 - (1 + delta) = -delta by ring] using h
    have h := intervalIntegral.integral_mono_on (by linarith : -y ≤ y)
      (f_vertical_integrable hchi X (1 + delta) y) intervalIntegrable_const
      (fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint t) 2)
    rw [intervalIntegral.integral_const] at h
    simpa only [smul_eq_mul, sub_neg_eq_add, ← two_mul] using h
  have h := sum_le_sum (s := nonprincipalCharacters q)
    (fun chi hchi => hi chi ((mem_nonprincipalCharacters chi).mp hchi))
  rw [sum_const, nsmul_eq_mul, card_nonprincipalCharacters] at h
  exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg q.totient)).trans_eq (by
    unfold nonprincipalRatio B
    ring)

@[simp] theorem Fmean_one (X sigma y : ℝ) : Fmean 1 X sigma y = 0 := by simp [Fmean]

@[simp] theorem Fmean_two (X sigma y : ℝ) : Fmean 2 X sigma y = 0 := by simp [Fmean]

end LiuWang.Proof.NonprincipalDensityMeans