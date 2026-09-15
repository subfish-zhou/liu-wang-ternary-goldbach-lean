import LiuWang.Proof.SourceRoute.HighSum.SourceParameters

/-! # The source lambda substitution and signed table integrals

The arithmetic coefficients below integrate the stated step bounds. They do
not assert that the actual family count satisfies the source tables.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum

theorem actual_lambda_substitution (N q : ℕ) [NeZero q] (y s a b : ℝ) :
    (∫ alpha in (1 - b / s)..(1 - a / s),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) =
      sourceL N / s * ∫ lam in a..b,
        (N : ℝ) ^ (-lam / s) * (familyCount q (1 - lam / s) y : ℝ) := by
  rw [← intervalIntegral.inv_smul_integral_comp_sub_div
    (fun alpha => layerKernel N alpha * (familyCount q alpha y : ℝ)) s 1]
  have he (lam : ℝ) :
      layerKernel N (1 - lam / s) * (familyCount q (1 - lam / s) y : ℝ) =
        sourceL N * ((N : ℝ) ^ (-lam / s) *
          (familyCount q (1 - lam / s) y : ℝ)) := by
    unfold layerKernel
    rw [show 1 - lam / s - 1 = -lam / s by ring]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  ring

theorem original_source29 (N q : ℕ) [NeZero q] (y c₁ : ℝ) :
    (∫ alpha in (1 - 0.478 / Real.log ((q : ℝ) * y))..
        (1 - 1 / (c₁ * Real.log ((q : ℝ) * y))),
      layerKernel N alpha * (familyCount q alpha y : ℝ)) =
      sourceL N / Real.log ((q : ℝ) * y) *
        ∫ lam in (1 / c₁)..(0.478 : ℝ),
          (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
            (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ) := by
  simpa only [div_div, one_div_mul_eq_div] using
    actual_lambda_substitution N q y (Real.log ((q : ℝ) * y)) (1 / c₁) 0.478

theorem original_alpha_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : omegaCutoff N q ≤ y) :
    (∫ alpha in (19 / 20 : ℝ)..1,
      layerKernel N alpha * (familyCount q alpha y : ℝ)) =
      (∫ alpha in (19 / 20 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * y)),
        layerKernel N alpha * (familyCount q alpha y : ℝ)) +
      sourceL N / Real.log ((q : ℝ) * y) *
        ∫ lam in (0 : ℝ)..(0.478 : ℝ),
          (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
            (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ) := by
  have hm := original_alpha_cutoff_mem hN hy
  have hi := family_alpha_integrable (q := q) (Parameters.nat_pos_of_exp_le hN) y
  have hleft := hi.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (by
    rw [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
    exact hm))
  have hright := hi.mono_set (Set.uIcc_subset_uIcc (by
    rw [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)]
    exact hm) Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  congr 1
  simpa only [zero_div, sub_zero] using
    actual_lambda_substitution N q y (Real.log ((q : ℝ) * y)) 0 0.478

theorem actual_lambda_integrable {N q : ℕ} [NeZero q]
    (hN : 1 < (N : ℝ)) (y : ℝ) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun lam =>
      (N : ℝ) ^ (-lam / s) * (familyCount q (1 - lam / s) y : ℝ))
      volume 0 (s / 20) := by
  have hn : 0 < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hL : sourceL N ≠ 0 := (Real.log_pos hN).ne'
  have hi := (family_alpha_integrable (q := q) hn y).div_const (sourceL N)
  have he (alpha : ℝ) :
      (layerKernel N alpha * (familyCount q alpha y : ℝ)) / sourceL N =
        (N : ℝ) ^ (alpha - 1) * (familyCount q alpha y : ℝ) := by
    unfold layerKernel
    field_simp
  simp_rw [he] at hi
  have ht := ((hi.comp_sub_left 1).comp_mul_left (c := 1 / s)).symm
  have hp (lam : ℝ) : 1 - lam / s - 1 = -lam / s := by ring
  simpa only [one_div_mul_eq_div, hp, sub_self, zero_div,
    show (1 - (19 / 20 : ℝ)) / (1 / s) = s / 20 by field_simp; ring] using ht

theorem split_source30 {f : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0.36)
    (hf : IntervalIntegrable f volume a 0.478) :
    (∫ lam in a..(0.478 : ℝ), f lam) =
      (∫ lam in a..(0.36 : ℝ), f lam) +
      (∫ lam in (0.36 : ℝ)..(0.39 : ℝ), f lam) +
      (∫ lam in (0.39 : ℝ)..(0.42 : ℝ), f lam) +
      (∫ lam in (0.42 : ℝ)..(0.45 : ℝ), f lam) +
      (∫ lam in (0.45 : ℝ)..(0.46 : ℝ), f lam) +
      (∫ lam in (0.46 : ℝ)..(0.47 : ℝ), f lam) +
      (∫ lam in (0.47 : ℝ)..(0.475 : ℝ), f lam) +
      (∫ lam in (0.475 : ℝ)..(0.478 : ℝ), f lam) := by
  have sub {c d : ℝ} (hc : a ≤ c) (hcd : c ≤ d) (hd : d ≤ 0.478) :
      IntervalIntegrable f volume c d := by
    apply hf.mono_set
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le (by linarith : a ≤ 0.478)]
    exact Set.Icc_subset_Icc hc hd
  have h0 := sub le_rfl ha (by norm_num : (0.36 : ℝ) ≤ 0.478)
  have h1 := sub ha (by norm_num : (0.36 : ℝ) ≤ 0.39) (by norm_num)
  have h2 := sub (by linarith : a ≤ 0.39) (by norm_num : (0.39 : ℝ) ≤ 0.42)
    (by norm_num)
  have h3 := sub (by linarith : a ≤ 0.42) (by norm_num : (0.42 : ℝ) ≤ 0.45)
    (by norm_num)
  have h4 := sub (by linarith : a ≤ 0.45) (by norm_num : (0.45 : ℝ) ≤ 0.46)
    (by norm_num)
  have h5 := sub (by linarith : a ≤ 0.46) (by norm_num : (0.46 : ℝ) ≤ 0.47)
    (by norm_num)
  have h6 := sub (by linarith : a ≤ 0.47) (by norm_num : (0.47 : ℝ) ≤ 0.475)
    (by norm_num)
  have h7 := sub (by linarith : a ≤ 0.475) (by norm_num : (0.475 : ℝ) ≤ 0.478)
    le_rfl
  rw [intervalIntegral.integral_add_adjacent_intervals h0 h1,
    intervalIntegral.integral_add_adjacent_intervals (h0.trans h1) h2,
    intervalIntegral.integral_add_adjacent_intervals ((h0.trans h1).trans h2) h3,
    intervalIntegral.integral_add_adjacent_intervals (((h0.trans h1).trans h2).trans h3) h4,
    intervalIntegral.integral_add_adjacent_intervals
      ((((h0.trans h1).trans h2).trans h3).trans h4) h5,
    intervalIntegral.integral_add_adjacent_intervals
      (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5) h6,
    intervalIntegral.integral_add_adjacent_intervals
      ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6) h7]

theorem original_source30_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (ha' : a ≤ 0.36) :
    IntervalIntegrable (fun lam =>
      (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
        (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ))
      volume a 0.478 := by
  have hs := original_log_product_ge_ten hN hy
  have hn1 : 1 < (N : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 3100)).trans_le hN
  apply (actual_lambda_integrable hn1 y (by linarith : 0 < Real.log ((q : ℝ) * y))).mono_set
  rw [Set.uIcc_of_le (by linarith : a ≤ 0.478),
    Set.uIcc_of_le (by positivity : 0 ≤ Real.log ((q : ℝ) * y) / 20)]
  exact Set.Icc_subset_Icc ha (by linarith)

theorem original_source30 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (ha' : a ≤ 0.36) :
    let f := fun lam =>
      (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y)) *
        (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ)
    (∫ lam in a..(0.478 : ℝ), f lam) =
      (∫ lam in a..(0.36 : ℝ), f lam) +
      (∫ lam in (0.36 : ℝ)..(0.39 : ℝ), f lam) +
      (∫ lam in (0.39 : ℝ)..(0.42 : ℝ), f lam) +
      (∫ lam in (0.42 : ℝ)..(0.45 : ℝ), f lam) +
      (∫ lam in (0.45 : ℝ)..(0.46 : ℝ), f lam) +
      (∫ lam in (0.46 : ℝ)..(0.47 : ℝ), f lam) +
      (∫ lam in (0.47 : ℝ)..(0.475 : ℝ), f lam) +
      (∫ lam in (0.475 : ℝ)..(0.478 : ℝ), f lam) :=
  split_source30 ha' (original_source30_integrable hN hy ha ha')

def lambdaSegment (L s a b : ℝ) : ℝ :=
  L / s * ∫ lam in a..b, Real.exp (-lam * L / s)

theorem lambdaSegment_eq {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (a b : ℝ) :
    lambdaSegment L s a b =
      Real.exp (-a * L / s) - Real.exp (-b * L / s) := by
  have hc : -L / s ≠ 0 := div_ne_zero (neg_ne_zero.mpr hL.ne') hs.ne'
  have he (lam : ℝ) : -lam * L / s = (-L / s) * lam := by ring
  unfold lambdaSegment
  simp_rw [he]
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem lambdaSegment_eq_source_power {N : ℕ} (hN : 0 < N) (s a b : ℝ) :
    lambdaSegment (sourceL N) s a b =
      sourceL N / s * ∫ lam in a..b, (N : ℝ) ^ (-lam / s) := by
  unfold lambdaSegment
  congr 1
  apply intervalIntegral.integral_congr
  intro lam _
  change Real.exp (-lam * sourceL N / s) = (N : ℝ) ^ (-lam / s)
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)]
  congr 1
  unfold sourceL
  ring

theorem source31_signed_segments {L s : ℝ} (hL : 0 < L) (hs : 0 < s) :
    35 * lambdaSegment L s 0.36 0.39 +
      89 * lambdaSegment L s 0.39 0.42 +
      182 * lambdaSegment L s 0.42 0.45 +
      292 * lambdaSegment L s 0.45 0.46 +
      664 * lambdaSegment L s 0.46 0.47 +
      1668 * lambdaSegment L s 0.47 0.475 +
      14000 * lambdaSegment L s 0.475 0.478 =
      35 * Real.exp (-0.36 * L / s) + 54 * Real.exp (-0.39 * L / s) +
      93 * Real.exp (-0.42 * L / s) + 110 * Real.exp (-0.45 * L / s) +
      372 * Real.exp (-0.46 * L / s) + 1004 * Real.exp (-0.47 * L / s) +
      12332 * Real.exp (-0.475 * L / s) - 14000 * Real.exp (-0.478 * L / s) := by
  simp only [lambdaSegment_eq hL hs]
  ring

theorem source35_signed_segments {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (c₁ : ℝ) :
    2 * lambdaSegment L s (1 / c₁) 0.3221 +
      13 * lambdaSegment L s 0.3221 0.33 +
      20 * lambdaSegment L s 0.33 0.36 =
      2 * Real.exp (-(1 / c₁) * L / s) +
      11 * Real.exp (-0.3221 * L / s) +
      7 * Real.exp (-0.33 * L / s) - 20 * Real.exp (-0.36 * L / s) := by
  simp only [lambdaSegment_eq hL hs]
  ring

end LiuWang.Proof.SourceRoute.HighSum
