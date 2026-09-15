import LiuWang.Proof.GlobalZeroDensity.Strip.ThreeLines

/-! The original positive-height window and its actual attained maximum. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open Complex.HadamardThreeLines
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.GlobalZeroDensity.Strip

def K (y σ : ℝ) : ℝ :=
  sSup ((fun t : ℝ => F y ((σ : ℂ) + t * Complex.I)) '' Icc (y - 3 / 2) (y + 3 / 2))

theorem norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos, norm_div]
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.I_im, mul_one, zero_sub, Complex.neg_im, neg_neg] at h
  rw [Real.cosh_eq]
  norm_num only [norm_ofNat]
  linarith

theorem cosh_near_half {x : ℝ} (hx0 : 4999 / 10000 ≤ x) (hx1 : x ≤ 5001 / 10000) :
    Real.cosh x ≤ 141 / 125 := by
  have heU := Real.exp_bound' (x := 5001 / 10000) (by norm_num) (by norm_num)
    (n := 6) (by norm_num)
  have heL := Real.sum_le_exp_of_nonneg (x := 4999 / 10000) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at heU heL
  have hmU := Real.exp_le_exp.mpr hx1
  have hmL := Real.exp_le_exp.mpr hx0
  have hu : Real.exp x ≤ 1649 / 1000 := by linarith
  have hl : 1000 / 607 ≤ Real.exp x := by linarith
  have hn : Real.exp (-x) ≤ 607 / 1000 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos x)).mpr
    linarith
  rw [Real.cosh_eq]
  linarith

theorem window_cos_bound {y t : ℝ} (hy : 10000 ≤ y)
    (ht : |t - y| ≤ 3 / 2) (σ : ℝ) :
    ‖Complex.cos (((σ : ℂ) + t * Complex.I) / (2 * (y : ℂ)))‖ ≤ 141 / 125 := by
  have hi : (((σ : ℂ) + t * Complex.I) / (2 * (y : ℂ))).im = t / (2 * y) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_im]
    simp
  apply (norm_cos_le_cosh _).trans
  rw [hi]
  have ht' := abs_le.mp ht
  apply cosh_near_half
  · apply (le_div_iff₀ (by positivity : 0 < 2 * y)).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * y)).mpr
    linarith

theorem window_F_le_regularG {y σ t : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (ht : |t - y| ≤ 3 / 2) :
    F y ((σ : ℂ) + t * Complex.I) ≤
      (14 / 11) * ‖regularG y ((σ : ℂ) + t * Complex.I)‖ ^ 2 := by
  let s := (σ : ℂ) + t * Complex.I
  have hd := delta_bounds hy
  have ht' := abs_le.mp ht
  have ht0 : 0 < t := by linarith
  have hs1 : s ≠ 1 := by intro h; have hh := congrArg Complex.im h; simp [s] at hh; linarith
  have hs : s ∈ verticalClosedStrip (1 / 2) (1 + delta y) := by
    simpa [s, verticalClosedStrip] using hσ
  have hden := strip_denominator_ne_zero (by linarith : 0 < y) (closed_strip_safe hy hs)
  have hsf : ‖f y s‖ ^ 2 =
      (‖s‖ ^ 2 / ‖s - 1‖ ^ 2) *
        ‖Complex.cos (s / (2 * (y : ℂ)))‖ ^ 2 * ‖regularG y s‖ ^ 2 := by
    rw [regularG_eq_g hs1, g, norm_mul, norm_div, norm_mul, mul_pow, div_pow, mul_pow]
    have hs0 : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr (left_ne_zero_of_mul hden)
    have hc0 : ‖Complex.cos (s / (2 * (y : ℂ)))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (right_ne_zero_of_mul hden)
    have h10 : ‖s - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)
    field_simp
  have hs2 : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    simp [s, Complex.sq_norm, Complex.normSq_apply]; ring
  have h12 : ‖s - 1‖ ^ 2 = (σ - 1) ^ 2 + t ^ 2 := by
    simp [s, Complex.sq_norm, Complex.normSq_apply]; ring
  have hratio : ‖s‖ ^ 2 / ‖s - 1‖ ^ 2 ≤ 10001 / 10000 := by
    rw [hs2, h12]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (t - 9998), hσ.1, hσ.2]
  have hcos := pow_le_pow_left₀ (norm_nonneg _) (window_cos_bound hy ht σ) 2
  have hm := mul_le_mul hratio hcos (sq_nonneg _) (by norm_num)
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖regularG y s‖)
  change ‖f y s‖ ^ 2 ≤ (14 / 11) * ‖regularG y s‖ ^ 2
  rw [hsf]
  nlinarith [sq_nonneg ‖regularG y s‖]

theorem F_window_left {y σ t : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) (ht : |t - y| ≤ 3 / 2) :
    F y ((σ : ℂ) + t * Complex.I) ≤
      42 * y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4) := by
  have hg := regularG_strip_source hy (s := (σ : ℂ) + t * Complex.I)
    (by simpa [verticalClosedStrip] using hσ)
  have h := window_F_le_regularG hy hσ ht
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] at hg
  nlinarith

theorem window_continuous {y : ℝ} (hy : 10000 ≤ y) (σ : ℝ) :
    ContinuousOn (fun t : ℝ => F y ((σ : ℂ) + t * Complex.I)) (Icc (y - 3 / 2) (y + 3 / 2)) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hs1 : (σ : ℂ) + t * Complex.I ≠ 1 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    linarith
  have hv : Continuous (fun t : ℝ => (σ : ℂ) + t * Complex.I) := by fun_prop
  have hf : ContinuousAt (fun t : ℝ => f y ((σ : ℂ) + t * Complex.I)) t :=
    ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * Complex.I) (g := f y)
      (differentiableAt_f y hs1).continuousAt hv.continuousAt
  exact (hf.norm.pow 2).continuousWithinAt

theorem K_attained {y : ℝ} (hy : 10000 ≤ y) (σ : ℝ) :
    ∃ t ∈ Icc (y - 3 / 2) (y + 3 / 2),
      K y σ = F y ((σ : ℂ) + t * Complex.I) ∧
        ∀ u ∈ Icc (y - 3 / 2) (y + 3 / 2),
          F y ((σ : ℂ) + u * Complex.I) ≤ K y σ := by
  have hne : (Icc (y - 3 / 2) (y + 3 / 2)).Nonempty := ⟨y, by constructor <;> linarith⟩
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne (window_continuous hy σ)
  have hbd := isCompact_Icc.bddAbove_image (window_continuous hy σ)
  have he : K y σ = F y ((σ : ℂ) + t * Complex.I) := by
    apply le_antisymm
    · apply csSup_le (hne.image _)
      rintro v ⟨u, hu, rfl⟩
      exact hmax hu
    · exact le_csSup hbd (mem_image_of_mem _ ht)
  exact ⟨t, ht, he, fun u hu => he.symm ▸ hmax hu⟩

theorem K_left {y σ : ℝ} (hy : 10000 ≤ y)
    (hσ : σ ∈ Icc (1 / 2) (1 + delta y)) :
    K y σ ≤ 42 * y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4) := by
  obtain ⟨t, ht, he, _⟩ := K_attained hy σ
  rw [he]
  apply F_window_left hy hσ
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem K_right {y σ : ℝ} (hy : 10000 ≤ y) (hσ : 1 + delta y ≤ σ) :
    K y σ ≤ (169 / 100) * Real.log y ^ 4 := by
  obtain ⟨t, _, he, _⟩ := K_attained hy σ
  rw [he]
  exact F_right_half hy (by simpa using hσ)

theorem lemma_3_3 {y σ : ℝ} (hy : 10000 * Real.log 6 ≤ y) :
    (1 / 2 ≤ σ ∧ σ ≤ 1 + delta y →
      K y σ ≤ (42021 / 1000) * y ^ (4 * (1 - σ)) * Real.log y ^ (8 * σ - 4)) ∧
    (1 + delta y ≤ σ ∧ σ ≤ 4 → K y σ ≤ (174 / 100) * Real.log y ^ 4) := by
  have hy' : 10000 ≤ y := by linarith [log_six_ge_one]
  constructor
  · intro hσ
    have h := K_left hy' hσ
    have hp := mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ y) (4 * (1 - σ)))
      (Real.rpow_nonneg (by have := log_ge_nine hy'; linarith : 0 ≤ Real.log y) (8 * σ - 4))
    nlinarith
  · intro hσ
    have h := K_right hy' hσ.1
    nlinarith [sq_nonneg (Real.log y ^ 2)]

end LiuWang.Proof.GlobalZeroDensity.Strip
