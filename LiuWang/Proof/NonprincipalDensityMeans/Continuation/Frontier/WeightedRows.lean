import LiuWang.Proof.NonprincipalDensityMeans.Continuation.ExplicitBound

/-! # Logarithmic rows retaining the individual index, on support n >= q -/

set_option autoImplicit false
noncomputable section

open Finset
open Classical

namespace LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier

theorem inverse_log_weight_le {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    1 / (m * |Real.log n - Real.log m|) ≤ 1 / m + 1 / |n - m| := by
  rcases lt_trichotomy n m with h | rfl | h
  · have hg := reciprocal_log_gap_le hn hm h.le le_rfl
    have hdiv := div_le_div_of_nonneg_right hg hm.le
    have he : (m / |n - m|) / m = 1 / |n - m| := by field_simp
    rw [he] at hdiv
    have he' : (1 / |Real.log n - Real.log m|) / m =
        1 / (m * |Real.log n - Real.log m|) := by ring
    rw [he'] at hdiv
    exact hdiv.trans (le_add_of_nonneg_left (by positivity))
  · simp [hn.le]
  · have hg := reciprocal_log_gap_le hn hm le_rfl h.le
    have hdiv := div_le_div_of_nonneg_right hg hm.le
    have he : (n / |n - m|) / m = 1 / m + 1 / |n - m| := by
      rw [abs_of_pos (sub_pos.mpr h)]
      field_simp
      ring
    rw [he] at hdiv
    have he' : (1 / |Real.log n - Real.log m|) / m =
        1 / (m * |Real.log n - Real.log m|) := by ring
    rwa [he'] at hdiv

theorem residue_inverse_row {q K : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ range K) (hlow : ∀ n ∈ S, q ≤ n) (x : ZMod q) :
    (∑ n ∈ fiber q S x, (n : ℝ)⁻¹) ≤
      (q : ℝ)⁻¹ * harmonicRange (K / q + 1) := by
  have hsub : (fiber q S x).image (fun n : ℕ => n / q) ⊆ range (K / q + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      (mem_range.mp (hS (mem_filter.mp hn).1)).le))
  have hpoint :
      (∑ n ∈ fiber q S x, (n : ℝ)⁻¹) ≤
        (q : ℝ)⁻¹ * ∑ k ∈ (fiber q S x).image (fun n : ℕ => n / q), (k : ℝ)⁻¹ := by
    rw [sum_image (quotient_inj_on_fiber q S x), mul_sum]
    apply sum_le_sum
    intro n hn
    have hquot : 0 < n / q := Nat.div_pos (hlow n (mem_filter.mp hn).1) (NeZero.pos q)
    have hp : (0 : ℝ) < (q : ℝ) * (n / q : ℕ) :=
      mul_pos (Nat.cast_pos.mpr (NeZero.pos q)) (Nat.cast_pos.mpr hquot)
    have hle : (q : ℝ) * (n / q : ℕ) ≤ n := by
      exact_mod_cast Nat.mul_div_le n q
    have h := one_div_le_one_div_of_le hp hle
    simpa only [one_div, mul_inv_rev, mul_comm] using h
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
    (by positivity))

theorem weighted_log_row {q K : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ range K) (hlow : ∀ n ∈ S, q ≤ n)
    (x : ZMod q) {n : ℕ} (hn : n ∈ fiber q S x) :
    (∑ m ∈ fiber q S x, 1 / ((m : ℝ) * |Real.log n - Real.log m|)) ≤
      3 / (q : ℝ) * harmonicRange (K / q + 1) := by
  have hn0 : 0 < n := (NeZero.pos q).trans_le (hlow n (mem_filter.mp hn).1)
  have hpoint :
      (∑ m ∈ fiber q S x, 1 / ((m : ℝ) * |Real.log n - Real.log m|)) ≤
      (∑ m ∈ fiber q S x, (m : ℝ)⁻¹) + ∑ m ∈ fiber q S x, 1 / |(n : ℝ) - m| := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro m hm
    simpa only [one_div] using inverse_log_weight_le (Nat.cast_pos.mpr hn0)
      (Nat.cast_pos.mpr ((NeZero.pos q).trans_le (hlow m (mem_filter.mp hm).1)))
  have h1 := residue_inverse_row hS hlow x
  have h2 := congruence_gap_row hS x hn
  exact hpoint.trans ((add_le_add h1 h2).trans_eq (by ring))

theorem indexed_two_mul_le {n m : ℝ} (hn : 0 < n) (hm : 0 < m) (a b : ℝ) :
    2 * a * b ≤ n / m * a ^ 2 + m / n * b ^ 2 := by
  apply (mul_le_mul_iff_left₀ (mul_pos hn hm)).mp
  field_simp
  nlinarith [sq_nonneg (n * a - m * b)]

theorem weighted_offDiagonal {q K : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ range K) (hlow : ∀ n ∈ S, q ≤ n) (x : ZMod q) (a : ℕ → ℂ) :
    (∑ n ∈ fiber q S x, ∑ m ∈ (fiber q S x).erase n,
      ‖a n‖ * ‖a m‖ / |Real.log n - Real.log m|) ≤
      3 / (q : ℝ) * harmonicRange (K / q + 1) *
        ∑ n ∈ fiber q S x, (n : ℝ) * ‖a n‖ ^ 2 := by
  let T := fiber q S x
  have hp (n : ℕ) (hn : n ∈ T) : (0 : ℝ) < n :=
    Nat.cast_pos.mpr ((NeZero.pos q).trans_le (hlow n (mem_filter.mp hn).1))
  have herase (n : ℕ) :
      (∑ m ∈ T.erase n, ‖a n‖ * ‖a m‖ / |Real.log n - Real.log m|) =
        ∑ m ∈ T, ‖a n‖ * ‖a m‖ / |Real.log n - Real.log m| := by
    apply sum_subset (erase_subset _ _)
    intro m hm hm'
    have : m = n := by simpa only [mem_erase, hm, and_true, not_not] using hm'
    simp [this]
  change (∑ n ∈ T, ∑ m ∈ T.erase n, _) ≤ _
  simp_rw [herase]
  have hpoint : 2 * (∑ n ∈ T, ∑ m ∈ T,
      ‖a n‖ * ‖a m‖ / |Real.log n - Real.log m|) ≤
      ∑ n ∈ T, ∑ m ∈ T,
        ((n : ℝ) / m * ‖a n‖ ^ 2 + (m : ℝ) / n * ‖a m‖ ^ 2) /
          |Real.log n - Real.log m| := by
    simp only [mul_sum]
    apply sum_le_sum
    intro n hn
    apply sum_le_sum
    intro m hm
    have h := div_le_div_of_nonneg_right (indexed_two_mul_le (hp n hn) (hp m hm) ‖a n‖ ‖a m‖)
      (abs_nonneg (Real.log n - Real.log m))
    simpa only [mul_div_assoc, mul_assoc] using h
  have hswap : (∑ n ∈ T, ∑ m ∈ T,
      ((m : ℝ) / n * ‖a m‖ ^ 2) / |Real.log n - Real.log m|) =
      ∑ n ∈ T, ∑ m ∈ T,
        ((n : ℝ) / m * ‖a n‖ ^ 2) / |Real.log n - Real.log m| := by
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    rw [abs_sub_comm]
  simp only [add_div, sum_add_distrib] at hpoint
  rw [hswap] at hpoint
  have hrow :
      (∑ n ∈ T, ∑ m ∈ T,
        ((n : ℝ) / m * ‖a n‖ ^ 2) / |Real.log n - Real.log m|) ≤
      3 / (q : ℝ) * harmonicRange (K / q + 1) * ∑ n ∈ T, (n : ℝ) * ‖a n‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have h := mul_le_mul_of_nonneg_left (weighted_log_row hS hlow x hn)
      (by positivity : 0 ≤ (n : ℝ) * ‖a n‖ ^ 2)
    simp only [mul_sum] at h
    simpa only [T, div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc, mul_comm,
      mul_left_comm] using h
  linarith

end LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier
