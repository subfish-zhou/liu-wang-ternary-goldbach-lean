import LiuWang.Proof.Campaign20260915.Density.PointRecovery

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

def chenMaximumBound (q : ℕ) (y sigma : ℝ) : ℝ :=
  47.202 * chenPointScale q y ^ (2 * (1 - sigma)) *
    Real.log ((q : ℝ) * y) ^ (8 * sigma - 4)

theorem log_le_quarter {L : ℝ} (hL : 11 ≤ L) : Real.log L ≤ L / 4 := by
  have hL0 : 0 < L := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < L / 11 by positivity)
  rw [Real.log_div hL0.ne' (by norm_num)] at h
  have h11 : Real.log (11 : ℝ) ≤ 2.5 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 11)
      (by norm_num : (11 : ℝ) ≤ 3 * 2 ^ 2)
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_three_lt_d9, Real.log_two_lt_d9]
  linarith

theorem chen_point_scale_ge_product (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y : ℝ} (hy : 1 ≤ y) : (q : ℝ) * y ≤ chenPointScale q y := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : 1 ≤ Real.log q := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
    linarith [Real.log_three_gt_d9]
  have hs : (1 : ℝ) ≤ Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq0.le).mpr (by exact_mod_cast (by omega : 1 ≤ q))
  have hm := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs hy) hl
  have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ (q : ℝ) * y by positivity)
  unfold chenPointScale
  nlinarith only [h]

theorem chenMaximumBound_antitone (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    Antitone (chenMaximumBound q y) := by
  have hy0 : 0 < y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy1 : 1 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < (q : ℝ) * y := by positivity
  have hD := chen_point_scale_ge_product q hq hy1
  have hD0 : 0 < chenPointScale q y := hX0.trans_le hD
  have hL := source_product_log_ge_eleven q hy
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith
  have hdlog := Real.log_le_log hX0 hD
  have hquarter := log_le_quarter hL
  intro a b hab
  have hm := mul_nonneg (sub_nonneg.mpr hab)
    (show 0 ≤ 2 * Real.log (chenPointScale q y) -
      8 * Real.log (Real.log ((q : ℝ) * y)) by linarith)
  have he (sigma : ℝ) : Real.log (chenMaximumBound q y sigma) =
      Real.log 47.202 + (2 * (1 - sigma)) * Real.log (chenPointScale q y) +
        (8 * sigma - 4) * Real.log (Real.log ((q : ℝ) * y)) := by
    unfold chenMaximumBound
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hD0, Real.log_rpow hL0]
  unfold chenMaximumBound
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  change Real.log (chenMaximumBound q y b) ≤ Real.log (chenMaximumBound q y a)
  rw [he, he]
  nlinarith only [hm]

theorem source_familyWindow_paid (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y sigma : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (hs : sigma ∈ Set.Icc (1 / 2) (1 + sourceDelta ((q : ℝ) * y))) :
    familyWindow q ((q : ℝ) * y) sigma y ≤ chenMaximumBound q y sigma := by
  apply csSup_le
  · exact ⟨_, ⟨y, ⟨by linarith, by linarith⟩, rfl⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    simpa [chenMaximumBound] using source_family_lemma_11 q hq hy
      (s := (sigma : ℂ) + t * I) (by simpa using hs)
      (by simpa using abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem source_familyMaximum_paid (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y a b : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (hab : a ≤ b) :
    familyMaximum q ((q : ℝ) * y) y a b ≤ chenMaximumBound q y a := by
  obtain ⟨sigma, hs, t, ht, he⟩ := familyMaximum_attained q ((q : ℝ) * y) y hab
  rw [he]
  by_cases hu : sigma ≤ 1 + sourceDelta ((q : ℝ) * y)
  · have h := source_family_lemma_11 q hq hy
      (s := (sigma : ℂ) + t * I) (by simpa using And.intro (ha.trans hs.1) hu)
      (by simpa using ht)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at h
    exact h.trans (chenMaximumBound_antitone q hq hy hs.1)
  · have hm := source_complete_f_point_right q hy
      (s := (sigma : ℂ) + t * I) (by simpa using (le_of_not_ge hu))
    have hf : familySquare q ((q : ℝ) * y) ((sigma : ℂ) + t * I) ≤
        1.947 * Real.log ((q : ℝ) * y) ^ 4 :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hm
    have h1 : 1.947 * Real.log ((q : ℝ) * y) ^ 4 ≤ chenMaximumBound q y 1 := by
      unfold chenMaximumBound
      norm_num
      nlinarith [sq_nonneg (Real.log ((q : ℝ) * y) ^ 2)]
    exact hf.trans (h1.trans (chenMaximumBound_antitone q hq hy ha1))

end LiuWang.Proof.Campaign20260915.Density
