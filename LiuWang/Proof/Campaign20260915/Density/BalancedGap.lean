import LiuWang.Proof.Campaign20260915.Density.Chen24
import LiuWang.Proof.NonprincipalDensityMeans.LogGaps

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.NonprincipalDensityMeans

namespace LiuWang.Proof.Campaign20260915.Density

theorem harmonic_upper_shift (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (n + 1) + 2 / 3 := by
  have h := (Real.eulerMascheroniSeq_lt_eulerMascheroniSeq' n 6).trans
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  unfold Real.eulerMascheroniSeq at h
  linarith

theorem reciprocal_range_eq_harmonic (n : ℕ) :
    (∑ k ∈ range (n + 1), (k : ℝ)⁻¹) = (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega : 1 ≤ n + 1)]
  simp

theorem reciprocal_gap_row_balanced {N m : ℕ} (hm : m < N) :
    (∑ n ∈ range N, 1 / |(m : ℝ) - n|) ≤ 2 * Real.log (((N : ℝ) + 1) / 2) + 4 / 3 := by
  let A := (range N).filter (fun n => n < m)
  let B := (range N).filter (fun n => ¬ n < m)
  have hl : (∑ n ∈ A, 1 / |(m : ℝ) - n|) ≤ (harmonic m : ℝ) := by
    have he : (∑ n ∈ A, 1 / |(m : ℝ) - n|) =
        ∑ k ∈ A.image (fun n => m - n), (k : ℝ)⁻¹ := by
      rw [sum_image (fun a ha b hb h => by
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        omega)]
      apply sum_congr rfl
      intro n hn
      have hn' : n < m := (mem_filter.mp hn).2
      have hreal : (n : ℝ) ≤ m := Nat.cast_le.mpr hn'.le
      rw [Nat.cast_sub hn'.le, abs_of_nonneg (by linarith), one_div]
    rw [he, ← reciprocal_range_eq_harmonic]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨n, _, rfl⟩ := mem_image.mp hk
      exact mem_range.mpr (by omega)
    · intro _ _ _
      positivity
  have hr : (∑ n ∈ B, 1 / |(m : ℝ) - n|) ≤ (harmonic (N - m - 1) : ℝ) := by
    have he : (∑ n ∈ B, 1 / |(m : ℝ) - n|) =
        ∑ k ∈ B.image (fun n => n - m), (k : ℝ)⁻¹ := by
      rw [sum_image (fun a ha b hb h => by
        have ha' := (mem_filter.mp ha).2
        have hb' := (mem_filter.mp hb).2
        omega)]
      apply sum_congr rfl
      intro n hn
      have hn' : m ≤ n := Nat.le_of_not_gt (mem_filter.mp hn).2
      have hreal : (m : ℝ) ≤ n := Nat.cast_le.mpr hn'
      rw [Nat.cast_sub hn', abs_of_nonpos (by linarith), neg_sub, one_div]
    rw [he, ← reciprocal_range_eq_harmonic]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
      have hnN := mem_range.mp (mem_filter.mp hn).1
      exact mem_range.mpr (by omega)
    · intro _ _ _
      positivity
  have hsplit := sum_filter_add_sum_filter_not (range N) (fun n => n < m)
    (fun n => 1 / |(m : ℝ) - n|)
  change (∑ n ∈ A, _) + (∑ n ∈ B, _) = _ at hsplit
  have hpos : (0 : ℝ) < (N - m : ℕ) := Nat.cast_pos.mpr (by omega)
  have hn : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := Nat.cast_sub hm.le
  have hp : ((m : ℝ) + 1) * (N - m : ℕ) ≤ (((N : ℝ) + 1) / 2) ^ 2 := by
    rw [hn]
    nlinarith [sq_nonneg (((m : ℝ) + 1) - (N - m))]
  have hlog := Real.log_le_log (mul_pos (by positivity : 0 < (m : ℝ) + 1) hpos) hp
  rw [Real.log_mul (by positivity) hpos.ne', Real.log_pow] at hlog
  have hH := harmonic_upper_shift (N - m - 1)
  rw [show ((N - m - 1 : ℕ) : ℝ) + 1 = (N - m : ℕ) by
    exact_mod_cast (show (N - m - 1 : ℕ) + 1 = N - m by omega)] at hH
  have hH' := harmonic_upper_shift m
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem source_congruence_gap_row {q : ℕ} [NeZero q] {y : ℝ} (hy : 10000 ≤ y)
    {S : Finset ℕ} (hS : S ⊆ range ⌈(q : ℝ) * y⌉₊) (x : ZMod q)
    {m : ℕ} (hm : m ∈ fiber q S x) :
    (∑ n ∈ fiber q S x, 1 / |(m : ℝ) - n|) ≤ (2 / q) * Real.log y := by
  let N : ℕ := ⌈(q : ℝ) * y⌉₊
  let K : ℕ := N / q + 1
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hy0 : 0 < y := by linarith
  have hmN : m < N := mem_range.mp (hS (mem_filter.mp hm).1)
  have hsub : (fiber q S x).image (fun n : ℕ => n / q) ⊆ range K := by
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
  have hN := (ceil_log_bounds (show 10000 ≤ (q : ℝ) * y by nlinarith)).1
  have hNq : (N : ℝ) / q ≤ 1.001 * y := by
    apply (div_le_iff₀ hq0).mpr
    dsimp [N]
    nlinarith only [hN]
  have hK : (K : ℝ) + 1 ≤ 1.01 * y := by
    have hd : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
    dsimp [K]
    push_cast
    linarith
  have hK0 : 0 < (K : ℝ) + 1 := by positivity
  have hlog : Real.log ((K : ℝ) + 1) ≤ Real.log y + 0.01 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hK0 hy0)
    rw [Real.log_div hK0.ne' hy0.ne'] at h
    have hd := (div_le_iff₀ hy0).mpr hK
    linarith
  have hbudget : 2 * Real.log (((K : ℝ) + 1) / 2) + 4 / 3 ≤ 2 * Real.log y := by
    rw [Real.log_div hK0.ne' (by norm_num)]
    linarith [Real.log_two_gt_d9]
  have hrow := (reciprocal_gap_row_balanced
    (Nat.lt_succ_of_le (Nat.div_le_div_right hmN.le) : m / q < K)).trans hbudget
  have hsmall := sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity : ∀ k ∈ range K,
      k ∉ (fiber q S x).image (fun n => n / q) → 0 ≤ 1 / |(m / q : ℕ) - (k : ℝ)|)
  rw [he]
  exact (mul_le_mul_of_nonneg_left (hsmall.trans hrow) (inv_nonneg.mpr hq0.le)).trans_eq (by ring)

end LiuWang.Proof.Campaign20260915.Density
