import LiuWang.Proof.GlobalZeroDensity.Sharp.ZetaTruncation

/-! Moving integer truncation gives a square-root height bound for the actual zeta function. -/

set_option autoImplicit false

noncomputable section

open Finset Complex

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem sum_inv_sqrt_endpoint (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, (Real.sqrt (n : ℝ))⁻¹) + (Real.sqrt (N : ℝ))⁻¹ ≤
      2 * Real.sqrt N - 1 := by
  have h : ∀ k : ℕ, (∑ n ∈ range (k + 2), (Real.sqrt (n : ℝ))⁻¹) ≤
      2 * Real.sqrt (k + 1 : ℕ) - 1 := by
    intro k
    induction k with
    | zero => norm_num [sum_range_succ]
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, sum_range_succ]
      have hb := inv_sqrt_le_difference
        (show (1 : ℝ) ≤ (k + 2 : ℕ) by exact_mod_cast (show 1 ≤ k + 2 by omega))
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
      have he : (k : ℝ) + 2 - 1 = k + 1 := by ring
      rw [he] at hb
      have he' : (k : ℝ) + 1 + 1 = k + 2 := by ring
      rw [he']
      linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hk := h k
  rwa [show k + 2 = (k + 1) + 1 by omega, sum_range_succ] at hk

theorem critical_norm_sub_one (t : ℝ) :
    ‖(1 / 2 : ℂ) + t * Complex.I - 1‖ = ‖(1 / 2 : ℂ) + t * Complex.I‖ := by
  have h : ‖(1 / 2 : ℂ) + t * Complex.I - 1‖ ^ 2 =
      ‖(1 / 2 : ℂ) + t * Complex.I‖ ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg ((1 / 2 : ℂ) + t * Complex.I - 1),
    norm_nonneg ((1 / 2 : ℂ) + t * Complex.I)]

theorem critical_norm_bounds (t : ℝ) :
    1 / 2 ≤ ‖(1 / 2 : ℂ) + t * Complex.I‖ ∧
      ‖(1 / 2 : ℂ) + t * Complex.I‖ ≤ 1 / 2 + |t| := by
  constructor
  · simpa using Complex.abs_re_le_norm ((1 / 2 : ℂ) + t * Complex.I)
  · simpa [norm_mul] using norm_add_le (1 / 2 : ℂ) ((t : ℂ) * Complex.I)

theorem norm_zeta_small_norm {t : ℝ}
    (ht : ‖(1 / 2 : ℂ) + t * Complex.I‖ ≤ 2) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ 3 := by
  have h := norm_zeta_centered_le (N := 1) (by norm_num) t
  rw [critical_norm_sub_one] at h
  norm_num at h
  have hl := (critical_norm_bounds t).1
  have hp : 0 < ‖(1 / 2 : ℂ) + t * Complex.I‖ := by linarith
  have hb : 1 / ‖(1 / 2 : ℂ) + t * Complex.I‖ ≤
      5 / 2 - ‖(1 / 2 : ℂ) + t * Complex.I‖ := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hl)]
  rw [one_div] at hb
  linarith

theorem moving_truncation_arithmetic {r a b : ℝ}
    (hr : 2 ≤ r) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha2 : a ^ 2 ≤ r / 2 + 1) (hb2 : b ^ 2 = r / 2) (hba : b ≤ a) :
    2 * a - 1 - (1 / 2) / a + a / r + r / a ≤ 4 * b := by
  have har : a ≤ r := by nlinarith
  have hd : a - b ≤ 1 / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hs : 2 * (a - b) ^ 2 ≤ 1 / 2 := by
    nlinarith [sq_nonneg (a - b - 1 / 2)]
  have hmain : 2 * a + r / a - (1 / 2) / a ≤ 4 * b := by
    apply (le_of_sub_nonpos ?_)
    have he :
        2 * a + r / a - (1 / 2) / a - 4 * b =
          (2 * (a - b) ^ 2 - 1 / 2) / a := by
      field_simp
      nlinarith
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hpole : a / r ≤ 1 := (div_le_one (by linarith)).mpr har
  linarith

theorem norm_zeta_large_norm {t : ℝ}
    (ht : 2 ≤ ‖(1 / 2 : ℂ) + t * Complex.I‖) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      4 * Real.sqrt (‖(1 / 2 : ℂ) + t * Complex.I‖ / 2) := by
  let r := ‖(1 / 2 : ℂ) + t * Complex.I‖
  let N : ℕ := ⌈r / 2⌉₊
  have hr : 2 ≤ r := ht
  have hceil : r / 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hceil' : (N : ℝ) < r / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have ha : 1 ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by linarith)
    simpa using h
  have hb : 1 ≤ Real.sqrt (r / 2) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ r / 2 by linarith)
    simpa using h
  have hba := Real.sqrt_le_sqrt hceil
  have ha2 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hb2 := Real.sq_sqrt (show 0 ≤ r / 2 by linarith)
  have h := norm_zeta_centered_le hN t
  rw [critical_norm_sub_one] at h
  have hsum := sum_inv_sqrt_endpoint N hN
  have harith := moving_truncation_arithmetic hr ha hb (by linarith) hb2 hba
  change ‖riemannZeta _‖ ≤ 4 * Real.sqrt (r / 2)
  change ‖riemannZeta _‖ ≤ _ + _ + _ / r + r / _ at h
  simp only [div_eq_mul_inv] at *
  linarith

theorem norm_zeta_sqrt_height (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
      3 * Real.sqrt (1 + |t|) := by
  have hs : 1 ≤ Real.sqrt (1 + |t|) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + |t| by linarith [abs_nonneg t])
    simpa only [Real.sqrt_one] using h
  by_cases ht : ‖(1 / 2 : ℂ) + t * Complex.I‖ ≤ 2
  · exact (norm_zeta_small_norm ht).trans (by linarith)
  · have h := norm_zeta_large_norm (le_of_not_ge ht)
    have hr := (critical_norm_bounds t).2
    have hb := Real.sq_sqrt
      (show 0 ≤ ‖(1 / 2 : ℂ) + t * Complex.I‖ / 2 by positivity)
    have ha := Real.sq_sqrt (show 0 ≤ 1 + |t| by positivity)
    have hcomp : 4 * Real.sqrt (‖(1 / 2 : ℂ) + t * Complex.I‖ / 2) ≤
        3 * Real.sqrt (1 + |t|) := by
      nlinarith [Real.sqrt_nonneg (‖(1 / 2 : ℂ) + t * Complex.I‖ / 2)]
    exact h.trans hcomp

end LiuWang.Proof.GlobalZeroDensity.Sharp
