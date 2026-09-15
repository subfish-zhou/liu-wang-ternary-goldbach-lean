import LiuWang.Proof.GlobalZeroDensity.Sharp.DetectorMean

/-! The four-divisibility sieve also reduces the number of off-diagonal rows. -/

set_option autoImplicit false

noncomputable section

open Finset Complex MeasureTheory

namespace LiuWang.Proof.GlobalZeroDensity.Sharp

theorem off_diagonal_sieved (N : ℕ) :
    (∑ m ∈ (range N).erase 0, ∑ n ∈ ((range N).erase 0).erase m,
      ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
      ((3 / 2) * N + 2) * (∑ k ∈ range N, (k : ℝ)⁻¹) + 2 * N := by
  let S := (range N).erase 0
  let A := (range (N / 4)).image (fun k : ℕ => 4 * k)
  let R := S \ A
  have hA : A ⊆ range N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    have hk' := mem_range.mp hk
    rw [mem_range]
    omega
  have hcardA : A.card = N / 4 := by
    rw [card_image_of_injective _ (fun a b h => by omega), card_range]
  have hR : R ⊆ range N := (sdiff_subset : R ⊆ S).trans (erase_subset _ _)
  have hc : (R.card : ℝ) ≤ (3 / 4) * N + 1 := by
    have hsub : R ⊆ range N \ A := by
      intro m hm
      exact mem_sdiff.mpr ⟨hR hm, (mem_sdiff.mp hm).2⟩
    have h := card_le_card hsub
    rw [card_sdiff_of_subset hA, card_range, hcardA] at h
    have h' : (R.card : ℝ) ≤ N - (N / 4 : ℕ) := by
      have hcast : (R.card : ℝ) ≤ ((N - N / 4 : ℕ) : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_sub (Nat.div_le_self N 4)] at hcast
    have hdiv : (N : ℝ) ≤ 4 * (N / 4 : ℕ) + 3 := by
      exact_mod_cast (show N ≤ 4 * (N / 4) + 3 by omega)
    linarith
  have hz (m : ℕ) (hm : m ∈ A) : criticalCoefficient m = 0 := by
    obtain ⟨k, _, rfl⟩ := mem_image.mp hm
    simp [criticalCoefficient, moebius_eq_zero_of_four_dvd (dvd_mul_right 4 k)]
  have heq : (∑ m ∈ R, ∑ n ∈ S.erase m,
      ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) =
      ∑ m ∈ S, ∑ n ∈ S.erase m,
      ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n| := by
    apply sum_subset sdiff_subset
    intro m hm hm'
    have hmA : m ∈ A := by
      by_contra h
      exact hm' (mem_sdiff.mpr ⟨hm, h⟩)
    simp [hz m hmA]
  change (∑ m ∈ S, _) ≤ _
  rw [← heq]
  have hb : (∑ m ∈ R, ∑ n ∈ S.erase m,
      ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
      ∑ m ∈ R, ∑ n ∈ range N,
        (1 / |(m : ℝ) - n| + 1 / (2 * Real.sqrt m * Real.sqrt n)) := by
    apply sum_le_sum
    intro m hm
    calc
      _ ≤ ∑ n ∈ S.erase m,
          (1 / |(m : ℝ) - n| + 1 / (2 * Real.sqrt m * Real.sqrt n)) := by
        apply sum_le_sum
        intro n hn
        exact coefficient_gap_le
          (Nat.pos_of_ne_zero (mem_erase.mp (mem_sdiff.mp hm).1).1)
          (Nat.pos_of_ne_zero (mem_erase.mp (mem_erase.mp hn).2).1)
          (mem_erase.mp hn).1.symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        ((erase_subset m S).trans (erase_subset 0 (range N))) (fun _ _ _ => by positivity)
  have hg : (∑ m ∈ R, ∑ n ∈ range N, 1 / |(m : ℝ) - n|) ≤
      ((3 / 2) * N + 2) * ∑ k ∈ range N, (k : ℝ)⁻¹ := by
    have h := sum_le_sum (fun m (hm : m ∈ R) => reciprocal_gap_row (mem_range.mp (hR hm)))
    simp only [sum_const, nsmul_eq_mul] at h
    have hh : 0 ≤ ∑ k ∈ range N, (k : ℝ)⁻¹ := sum_nonneg (fun _ _ => by positivity)
    have hmul := mul_le_mul_of_nonneg_right hc hh
    nlinarith
  have hs : (∑ m ∈ R, ∑ n ∈ range N, 1 / (2 * Real.sqrt m * Real.sqrt n)) ≤ 2 * N :=
    (sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => sum_nonneg (fun _ _ => by positivity))).trans
      (smooth_kernel_sum_le N)
  simp only [sum_add_distrib] at hb
  linarith

theorem Q_mean_sieved (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in -u..u, ‖Q y ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (2 * u + 3 * (⌈y⌉₊ : ℝ) + 4) * (1 + Real.log ⌈y⌉₊) + 4 * (⌈y⌉₊ : ℝ) := by
  have he := mul_le_mul_of_nonneg_left (mollifier_energy_le_inverse_range ⌈y⌉₊)
    (show 0 ≤ 2 * u by positivity)
  have ho := off_diagonal_sieved ⌈y⌉₊
  have h := Q_mean_diagonal_offDiagonal y hu
  have hlog := mul_le_mul_of_nonneg_left (inverse_range_le_log ⌈y⌉₊)
    (show 0 ≤ 2 * u + 3 * (⌈y⌉₊ : ℝ) + 4 by positivity)
  nlinarith

theorem sieved_mean_budget {y u : ℝ} (hy : 10000 ≤ y) (hu : 0 ≤ u) :
    (2 * (y * u) + 3 * (⌈y⌉₊ : ℝ) + 4) * (1 + Real.log ⌈y⌉₊) +
        4 * (⌈y⌉₊ : ℝ) ≤
      y * Real.log y * ((9 / 4) * u + 4) := by
  have hy0 : 0 ≤ y := by linarith
  have hlog := log_ge_nine hy
  obtain ⟨hN, hlN⟩ := ceil_log_bounds hy
  have h1 : 2 * (y * u) + 3 * (⌈y⌉₊ : ℝ) + 4 ≤ y * (2 * u + 301 / 100) := by
    nlinarith
  have h2 : 1 + Real.log ⌈y⌉₊ ≤ (139 / 125) * Real.log y := by linarith
  have h0 : 0 ≤ 1 + Real.log ⌈y⌉₊ := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ ⌈y⌉₊ by have := Nat.le_ceil y; linarith)
    linarith
  have hp := mul_le_mul h1 h2 h0 (show 0 ≤ y * (2 * u + 301 / 100) by positivity)
  have hlmul := mul_le_mul_of_nonneg_left hlog hy0
  have huyl := mul_nonneg hu
    (show 0 ≤ y * Real.log y by positivity)
  nlinarith

theorem lemma_3_4 {y : ℝ} (hy : 10000 * Real.log 6 ≤ y) {u : ℝ} (hu : 0 ≤ u) :
    M y (1 / 2) (y * u) ≤
      (12508 / 1000) * y * (2 + y * u) *
        ((219021 / 100000) * u + 2906 / 1000) * Real.log y := by
  have hy' : 10000 ≤ y := by linarith [log_six_ge_one]
  have hy0 : 0 ≤ y := by linarith
  have hT : 0 ≤ y * u := mul_nonneg hy0 hu
  have hlog := log_ge_nine hy'
  have h := M_critical_le_Q_mean y hT
  have hq := (Q_mean_sieved y hT).trans (sieved_mean_budget hy' hu)
  have hm := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ (202 / 25) * (2 + y * u) by positivity)
  have he : 202 * y * u ≤ y * Real.log y * (2 + y * u) := by
    have hyl : 202 ≤ y * Real.log y := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hyl hT
    nlinarith [mul_nonneg hy0 (show 0 ≤ Real.log y by linarith)]
  have hc : (202 / 25) * ((9 / 4) * u + 4) + 1 ≤
      (12508 / 1000) * ((219021 / 100000) * u + 2906 / 1000) := by nlinarith
  have hpaid := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ y * Real.log y * (2 + y * u) by positivity)
  nlinarith

end LiuWang.Proof.GlobalZeroDensity.Sharp
