import LiuWang.Proof.NonprincipalDensityMeans.FiniteMean
import LiuWang.Proof.GlobalZeroDensity.Sharp.HarmonicGaps

/-! # The q-spaced logarithmic kernel on an actual residue fiber -/

set_option autoImplicit false
noncomputable section

open Finset
open Classical
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.NonprincipalDensityMeans

theorem residue_real_difference {q m n : ℕ}
    (he : (m : ZMod q) = (n : ZMod q)) :
    (m : ℝ) - n = (q : ℝ) * ((m / q : ℕ) - (n / q : ℕ) : ℝ) := by
  have hr := (ZMod.natCast_eq_natCast_iff' m n q).mp he
  have hm : ((m % q : ℕ) : ℝ) + (q : ℝ) * (m / q : ℕ) = m := by
    exact_mod_cast Nat.mod_add_div m q
  have hn : ((n % q : ℕ) : ℝ) + (q : ℝ) * (n / q : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n q
  rw [hr] at hm
  linarith

theorem quotient_inj_on_fiber (q : ℕ) (S : Finset ℕ) (x : ZMod q) :
    Set.InjOn (fun n : ℕ => n / q) (fiber q S x) := by
  intro m hm n hn he
  change m / q = n / q at he
  have hr := residue_real_difference ((mem_filter.mp hm).2.trans (mem_filter.mp hn).2.symm)
  rw [he, sub_self, mul_zero, sub_eq_zero] at hr
  exact_mod_cast hr

def harmonicRange (N : ℕ) : ℝ := ∑ k ∈ range N, (k : ℝ)⁻¹

theorem harmonicRange_nonneg (N : ℕ) : 0 ≤ harmonicRange N :=
  sum_nonneg (fun _ _ => by positivity)

theorem congruence_gap_row {q N : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ range N) (x : ZMod q) {m : ℕ} (hm : m ∈ fiber q S x) :
    (∑ n ∈ fiber q S x, 1 / |(m : ℝ) - n|) ≤
      2 / (q : ℝ) * harmonicRange (N / q + 1) := by
  have hmN := mem_range.mp (hS (mem_filter.mp hm).1)
  have hsub : (fiber q S x).image (fun n : ℕ => n / q) ⊆ range (N / q + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hnN := mem_range.mp (hS (mem_filter.mp hn).1)
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le))
  have he :
      (∑ n ∈ fiber q S x, 1 / |(m : ℝ) - n|) =
        (q : ℝ)⁻¹ * ∑ k ∈ (fiber q S x).image (fun n : ℕ => n / q),
          1 / |(m / q : ℕ) - (k : ℝ)| := by
    rw [sum_image (quotient_inj_on_fiber q S x), mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [residue_real_difference ((mem_filter.mp hm).2.trans (mem_filter.mp hn).2.symm),
      abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    simp only [one_div, mul_inv_rev]
    ring
  rw [he]
  have hrow := reciprocal_gap_row
    (Nat.lt_succ_of_le (Nat.div_le_div_right hmN.le) : m / q < N / q + 1)
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => by positivity : ∀ k ∈ range (N / q + 1),
      k ∉ (fiber q S x).image (fun n => n / q) → 0 ≤ 1 / |(m / q : ℕ) - (k : ℝ)|)
  have h := mul_le_mul_of_nonneg_left (hsum.trans hrow) (inv_nonneg.mpr (Nat.cast_nonneg q))
  simpa only [harmonicRange, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem reciprocal_log_gap_le {x z B : ℝ} (hx : 0 < x) (hz : 0 < z)
    (hxB : x ≤ B) (hzB : z ≤ B) :
    1 / |Real.log x - Real.log z| ≤ B / |x - z| := by
  have hordered {v u : ℝ} (hv : 0 < v) (hvu : v < u) (huB : u ≤ B) :
      1 / (Real.log u - Real.log v) ≤ B / (u - v) := by
    have hu := hv.trans hvu
    have hlog := Real.log_le_sub_one_of_pos (div_pos hv hu)
    rw [Real.log_div hv.ne' hu.ne'] at hlog
    have hlow : 1 - (Real.log u - Real.log v) ≤ v / u := by linarith
    have hprod := (le_div_iff₀ hu).mp hlow
    have hL := sub_pos.mpr (Real.log_lt_log hv hvu)
    have hB := mul_le_mul_of_nonneg_right huB hL.le
    apply (div_le_div_iff₀ hL (sub_pos.mpr hvu)).mpr
    nlinarith
  rcases lt_trichotomy x z with h | rfl | h
  · rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hx h)),
      abs_of_neg (sub_neg.mpr h), neg_sub, neg_sub]
    exact hordered hx h hzB
  · simp
  · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hz h)), abs_of_pos (sub_pos.mpr h)]
    exact hordered hz h hxB

def logRowBound (q N : ℕ) : ℝ :=
  2 * (N : ℝ) / q * harmonicRange (N / q + 1)

theorem logRowBound_nonneg (q N : ℕ) : 0 ≤ logRowBound q N := by
  unfold logRowBound
  exact mul_nonneg (by positivity) (harmonicRange_nonneg _)

theorem log_gap_row {q N : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) (x : ZMod q) {m : ℕ} (hm : m ∈ fiber q S x) :
    (∑ n ∈ fiber q S x, 1 / |Real.log m - Real.log n|) ≤ logRowBound q N := by
  have hmS := hS (mem_filter.mp hm).1
  have hpoint : (∑ n ∈ fiber q S x, 1 / |Real.log m - Real.log n|) ≤
      (N : ℝ) * ∑ n ∈ fiber q S x, 1 / |(m : ℝ) - n| := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hnS := hS (mem_filter.mp hn).1
    simpa only [mul_one_div] using reciprocal_log_gap_le
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (mem_erase.mp hmS).1))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (mem_erase.mp hnS).1))
      (Nat.cast_le.mpr (mem_range.mp (mem_erase.mp hmS).2).le)
      (Nat.cast_le.mpr (mem_range.mp (mem_erase.mp hnS).2).le)
  have hrow := congruence_gap_row (hS.trans (erase_subset _ _)) x hm
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg _)).trans_eq (by
    unfold logRowBound
    ring))

theorem symmetric_weighted_kernel_le (S : Finset ℕ) (a : ℕ → ℂ)
    (K : ℕ → ℕ → ℝ) (hK : ∀ m n, 0 ≤ K m n)
    (hsym : ∀ m n, K m n = K n m) {R : ℝ}
    (hrow : ∀ m ∈ S, (∑ n ∈ S, K m n) ≤ R) :
    (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ * ‖a n‖ * K m n) ≤
      R * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  have hpoint :
      2 * (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ * ‖a n‖ * K m n) ≤
        ∑ m ∈ S, ∑ n ∈ S, (‖a m‖ ^ 2 + ‖a n‖ ^ 2) * K m n := by
    simp only [mul_sum]
    apply sum_le_sum
    intro m _
    apply sum_le_sum
    intro n _
    have h := mul_le_mul_of_nonneg_right
      (show 2 * ‖a m‖ * ‖a n‖ ≤ ‖a m‖ ^ 2 + ‖a n‖ ^ 2 by nlinarith [sq_nonneg (‖a m‖ - ‖a n‖)])
      (hK m n)
    nlinarith only [h]
  have hswap :
      (∑ m ∈ S, ∑ n ∈ S, ‖a n‖ ^ 2 * K m n) =
        ∑ m ∈ S, ∑ n ∈ S, ‖a m‖ ^ 2 * K m n := by
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    rw [hsym n m]
  simp only [add_mul, sum_add_distrib] at hpoint
  rw [hswap] at hpoint
  have hmain : (∑ m ∈ S, ∑ n ∈ S, ‖a m‖ ^ 2 * K m n) ≤
      R * ∑ m ∈ S, ‖a m‖ ^ 2 := by
    simp only [← mul_sum]
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)
  linarith

theorem fiber_offDiagonal_le {q N : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) (x : ZMod q) (a : ℕ → ℂ) :
    (∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
      ‖a m‖ * ‖a n‖ / |Real.log m - Real.log n|) ≤
        logRowBound q N * ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 := by
  have h := symmetric_weighted_kernel_le (fiber q S x) a
    (fun m n => 1 / |Real.log m - Real.log n|)
    (fun _ _ => by positivity)
    (fun m n => by rw [abs_sub_comm])
    (fun _ hm => log_gap_row hS x hm)
  have he (m : ℕ) :
      (∑ n ∈ (fiber q S x).erase m, ‖a m‖ * ‖a n‖ / |Real.log m - Real.log n|) =
        ∑ n ∈ fiber q S x, ‖a m‖ * ‖a n‖ / |Real.log m - Real.log n| := by
    apply sum_subset (erase_subset _ _)
    intro n hn hn'
    have : n = m := by simpa only [mem_erase, hn, and_true, not_not] using hn'
    simp [this]
  simp_rw [he]
  simpa only [mul_one_div] using h

end LiuWang.Proof.NonprincipalDensityMeans
