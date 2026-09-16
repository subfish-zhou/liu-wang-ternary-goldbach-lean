import LiuWang.Proof.Campaign20260915.RosserCount.BacklundReflection

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter MeasureTheory Finset
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.ZetaWinding

theorem gamma_reciprocal_difference_bound {z w : ℂ}
    (hz : (1 / 2 : ℝ) ≤ z.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hy : 0 < z.im) (him : w.im = z.im) (n : ℕ) :
    ‖(w + n)⁻¹ - (z + n)⁻¹‖ ≤
      2 * ‖z - w‖ * (1 / ((n : ℝ) + z.im) - 1 / ((n : ℝ) + z.im + 1)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hzn : z + n ≠ 0 := ne_zero_of_re_pos (by simp only [add_re, natCast_re]; linarith)
  have hwn : w + n ≠ 0 := ne_zero_of_re_pos (by simp only [add_re, natCast_re]; linarith)
  let D : ℝ := ((n : ℝ) + 1 / 2) ^ 2 + z.im ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hzD : D ≤ ‖z + n‖ ^ 2 := by
    rw [← normSq_eq_norm_sq]
    simp only [normSq_apply, add_re, add_im, natCast_re, natCast_im, add_zero]
    dsimp [D]
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 / 2)
      (by linarith : (n : ℝ) + 1 / 2 ≤ z.re + n) 2]
  have hwD : D ≤ ‖w + n‖ ^ 2 := by
    rw [← normSq_eq_norm_sq]
    simp only [normSq_apply, add_re, add_im, natCast_re, natCast_im, add_zero, him]
    dsimp [D]
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 / 2)
      (by linarith : (n : ℝ) + 1 / 2 ≤ w.re + n) 2]
  have hprod : D ≤ ‖w + n‖ * ‖z + n‖ := by
    apply (sq_le_sq₀ hD (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    nlinarith only [mul_le_mul hwD hzD hD (sq_nonneg ‖w + n‖)]
  have hden : ((n : ℝ) + z.im) * ((n : ℝ) + z.im + 1) ≤
      2 * (‖w + n‖ * ‖z + n‖) := by
    have hs : ((n : ℝ) + z.im) * ((n : ℝ) + z.im + 1) ≤ 2 * D := by
      dsimp [D]
      nlinarith [sq_nonneg ((n : ℝ) - z.im + 1 / 2)]
    linarith
  have he : (w + n)⁻¹ - (z + n)⁻¹ = (z - w) / ((w + n) * (z + n)) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul]
  calc
    _ ≤ 2 * ‖z - w‖ / (((n : ℝ) + z.im) * ((n : ℝ) + z.im + 1)) := by
      apply (div_le_div_iff₀
        (mul_pos (norm_pos_iff.mpr hwn) (norm_pos_iff.mpr hzn)) (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hden (norm_nonneg (z - w))]
    _ = _ := by
      field_simp
      ring

theorem digamma_horizontal_difference_bound {z w : ℂ}
    (hz : (1 / 2 : ℝ) ≤ z.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hy : 0 < z.im) (him : w.im = z.im) :
    ‖digamma z - digamma w‖ ≤ 2 * ‖z - w‖ / z.im := by
  have hs := (hasSum_digamma_of_re_pos (by linarith : 0 < z.re)).sub
    (hasSum_digamma_of_re_pos (by linarith : 0 < w.re))
  have ht : Tendsto (fun N : ℕ => ∑ n ∈ range N, ((w + n)⁻¹ - (z + n)⁻¹))
      atTop (𝓝 (digamma z - digamma w)) := by
    convert! hs.tendsto_sum_nat using 1
    · funext N
      apply Finset.sum_congr rfl
      intro n _
      ring
    · congr 1
      ring
  have hfinite (N : ℕ) :
      ‖∑ n ∈ range N, ((w + n)⁻¹ - (z + n)⁻¹)‖ ≤
        2 * ‖z - w‖ * (1 / z.im - 1 / ((N : ℝ) + z.im)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hb := gamma_reciprocal_difference_bound hz hw hy him N
      have htri := norm_add_le
        (∑ n ∈ range N, ((w + n)⁻¹ - (z + n)⁻¹)) ((w + N)⁻¹ - (z + N)⁻¹)
      have he : ((N + 1 : ℕ) : ℝ) + z.im = (N : ℝ) + z.im + 1 := by
        push_cast
        ring
      rw [he]
      linarith
  apply le_of_tendsto ht.norm
  apply Filter.Eventually.of_forall
  intro N
  have hb := hfinite N
  have hn : 0 ≤ 2 * ‖z - w‖ * (1 / ((N : ℝ) + z.im)) := by positivity
  simp only [div_eq_mul_inv] at hb hn ⊢
  nlinarith

theorem backlundArchSlope_reflection_bound {T u : ℝ} (hT : 0 < T)
    (hu : u ∈ Set.Icc (0 : ℝ) (3 / 4)) :
    |backlundArchSlope T (1 / 2 - u) - backlundArchSlope T (1 / 2 + u)| ≤
      2 * u / T ^ 2 + 2 * u / T := by
  have hu0 : 0 ≤ u := hu.1
  let p := horizontalAt T (1 / 2 - u) - 1
  let q := horizontalAt T (1 / 2 + u) - 1
  let z := horizontalAt T (1 / 2 - u) / 2 + 1
  let w := horizontalAt T (1 / 2 + u) / 2 + 1
  have hp : T ≤ ‖p‖ := by simpa [p, horizontalAt] using im_le_norm p
  have hq : T ≤ ‖q‖ := by simpa [q, horizontalAt] using im_le_norm q
  have hp0 : p ≠ 0 := norm_pos_iff.mp (hT.trans_le hp)
  have hq0 : q ≠ 0 := norm_pos_iff.mp (hT.trans_le hq)
  have hqp : ‖q - p‖ = 2 * u := by
    have he : q - p = ((2 * u : ℝ) : ℂ) := by
      dsimp [p, q, horizontalAt]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hrec : ‖p⁻¹ - q⁻¹‖ ≤ 2 * u / T ^ 2 := by
    have he : p⁻¹ - q⁻¹ = (q - p) / (p * q) := by field_simp
    rw [he, norm_div, norm_mul, hqp]
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hT)
    simpa only [pow_two] using mul_le_mul hp hq hT.le (norm_nonneg p)
  have hz : (1 / 2 : ℝ) ≤ z.re := by simp [z, horizontalAt]; linarith [hu.2]
  have hw : (1 / 2 : ℝ) ≤ w.re := by simp [w, horizontalAt]; linarith [hu.1]
  have hzim : z.im = T / 2 := by simp [z, horizontalAt]
  have hwim : w.im = z.im := by simp [w, z, horizontalAt]
  have hzw : ‖z - w‖ = u := by
    have he : z - w = ((-u : ℝ) : ℂ) := by
      dsimp [z, w, horizontalAt]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hu.1]
  have hg : ‖digamma z - digamma w‖ ≤ 4 * u / T := by
    have hh := digamma_horizontal_difference_bound hz hw
      (by rw [hzim]; positivity) hwim
    rw [hzw, hzim] at hh
    convert! hh using 1
    field_simp
    ring
  have he : backlundArchSlope T (1 / 2 - u) - backlundArchSlope T (1 / 2 + u) =
      ((p⁻¹ - q⁻¹) + (1 / 2 : ℂ) * (digamma z - digamma w)).im := by
    simp only [backlundArchSlope, p, q, z, w, one_div, add_im, sub_im, mul_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖(p⁻¹ - q⁻¹) + (1 / 2 : ℂ) * (digamma z - digamma w)‖ := abs_im_le_norm _
    _ ≤ ‖p⁻¹ - q⁻¹‖ + ‖(1 / 2 : ℂ) * (digamma z - digamma w)‖ := norm_add_le _ _
    _ = ‖p⁻¹ - q⁻¹‖ + (1 / 2 : ℝ) * ‖digamma z - digamma w‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 2 * u / T ^ 2 + (1 / 2 : ℝ) * (4 * u / T) :=
      add_le_add hrec (mul_le_mul_of_nonneg_left hg (by norm_num))
    _ = _ := by ring

theorem backlundLog_reflection_defect_lt_four_div {T : ℝ} (hT : 1 ≤ T)
    (hr : ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| = T → riemannZeta s ≠ 0)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) :
    |((backlundLog T (1 / 2 + δ)).im - (backlundLog T (1 / 2)).im) +
      ((backlundLog T (1 / 2 - δ)).im - (backlundLog T (1 / 2)).im)| < 4 / T := by
  have hpos : 0 < T := by linarith
  rw [backlundLog_reflection_defect hpos hr hδ]
  have hb (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) δ) :
      |backlundArchSlope T (1 / 2 - u) - backlundArchSlope T (1 / 2 + u)| ≤ 3 / T := by
    have hu0 : 0 ≤ u := hu.1
    have hh := backlundArchSlope_reflection_bound hpos ⟨hu.1, hu.2.trans hδ.2⟩
    have ht : T ≤ T ^ 2 := by nlinarith
    have hsmall : 2 * u / T ^ 2 ≤ 2 * u / T :=
      div_le_div_of_nonneg_left (by positivity) hpos ht
    refine hh.trans ?_
    calc
      _ ≤ 2 * u / T + 2 * u / T := add_le_add hsmall le_rfl
      _ = 4 * u / T := by ring
      _ ≤ 3 / T := (div_le_div_iff_of_pos_right hpos).mpr (by linarith [hu.2, hδ.2])
  have hi :
      |∫ u in (0 : ℝ)..δ, backlundArchSlope T (1 / 2 - u) -
        backlundArchSlope T (1 / 2 + u)| ≤ δ * (3 / T) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := δ) (C := 3 / T)
      (f := fun u => backlundArchSlope T (1 / 2 - u) - backlundArchSlope T (1 / 2 + u))
      (fun u hu => by
        rw [Real.norm_eq_abs]
        apply hb
        simpa only [Set.uIcc_of_le hδ.1] using Set.uIoc_subset_uIcc hu)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hδ.1, mul_comm] using hh
  refine hi.trans_lt ?_
  calc
    _ ≤ (3 / 4 : ℝ) * (3 / T) :=
      mul_le_mul_of_nonneg_right hδ.2 (by positivity)
    _ = (9 / 4 : ℝ) / T := by ring
    _ < 4 / T := (div_lt_div_iff_of_pos_right hpos).mpr (by norm_num)

#print axioms gamma_reciprocal_difference_bound
#print axioms digamma_horizontal_difference_bound
#print axioms backlundArchSlope_reflection_bound
#print axioms backlundLog_reflection_defect_lt_four_div

end LiuWang.Proof.Campaign20260915.RosserCount
