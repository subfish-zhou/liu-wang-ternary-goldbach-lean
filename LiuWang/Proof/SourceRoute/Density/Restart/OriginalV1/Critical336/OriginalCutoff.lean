import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.RealCutoff
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336.FiniteSum

set_option autoImplicit false
noncomputable section

open Complex

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336

theorem half_line_norm_geometry (t : ℝ) :
    1 / 2 ≤ ‖(1 / 2 : ℂ) + t * I‖ ∧
    ‖(1 / 2 : ℂ) + t * I - 1‖ = ‖(1 / 2 : ℂ) + t * I‖ ∧
    ‖(1 / 2 : ℂ) + t * I‖ ≤ 1 / 2 + |t| := by
  constructor
  · have h := Complex.re_le_norm ((1 / 2 : ℂ) + t * I)
    norm_num at h ⊢
    exact h
  constructor
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [Complex.sq_norm, Complex.normSq_apply]
    norm_num
  · have h := norm_add_le (1 / 2 : ℂ) ((t : ℂ) * I)
    simpa using h

theorem half_line_real_cutoff_bound {N : ℝ} (hN : 0 < N) (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      2 * Real.sqrt N + ‖(1 / 2 : ℂ) + t * I‖ / Real.sqrt N +
        Real.sqrt N / ‖(1 / 2 : ℂ) + t * I‖ + 1 / (2 * Real.sqrt N) := by
  let s : ℂ := (1 / 2 : ℂ) + t * I
  have hs : s.re = 1 / 2 := by simp [s]
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; rw [hs] at this; norm_num at this
  have hnneg : ‖(N : ℂ) ^ (-s)‖ = (Real.sqrt N)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re, hs,
      Real.rpow_neg hN.le, Real.sqrt_eq_rpow]
  have hnpos : ‖(N : ℂ) ^ (1 - s)‖ = Real.sqrt N := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    simp only [Complex.sub_re, Complex.one_re, hs]
    norm_num
    exact (Real.sqrt_eq_rpow N).symm
  have hr : ‖realRemainder N s‖ ≤ (Real.sqrt N)⁻¹ := by
    simpa [hs, Real.rpow_neg hN.le, Real.sqrt_eq_rpow] using realRemainder_norm_le hN hs0
  have hb : ‖(bernoulliBoundary N : ℂ) * (N : ℂ) ^ (-s)‖ ≤ 1 / (2 * Real.sqrt N) := by
    rw [norm_mul, Complex.norm_real, hnneg]
    have h := mul_le_mul_of_nonneg_right (bernoulliBoundary_norm N)
      (inv_nonneg.mpr (Real.sqrt_nonneg N))
    convert! h using 1
    ring
  have hz := real_cutoff_identity hN hs0 hs1
  have he : riemannZeta s =
      (∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (n : ℂ) ^ (-s)) +
        s * realRemainder N s + (N : ℂ) ^ (1 - s) / (s - 1) -
          (bernoulliBoundary N : ℂ) * (N : ℂ) ^ (-s) := by linear_combination hz
  calc
    _ ≤ ‖∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (n : ℂ) ^ (-s)‖ +
        ‖s * realRemainder N s‖ + ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ +
          ‖(bernoulliBoundary N : ℂ) * (N : ℂ) ^ (-s)‖ := by
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      rw [norm_mul, norm_div, hnpos, show ‖s - 1‖ = ‖s‖ from (half_line_norm_geometry t).2.1]
      have hrem := mul_le_mul_of_nonneg_left hr (norm_nonneg s)
      have hsum := finite_critical_sum hN.le t
      dsimp [s] at *
      rw [div_eq_mul_inv ‖(1 / 2 : ℂ) + t * I‖]
      linarith

theorem original_cutoff_positive (t : ℝ) : 0 < ‖(1 / 2 : ℂ) + t * I‖ / 2 := by
  linarith [(half_line_norm_geometry t).1]

theorem original_cutoff_at_zero : ‖(1 / 2 : ℂ) + (0 : ℝ) * I‖ / 2 = 1 / 4 := by
  norm_num

theorem equation_3_36_at_original_cutoff (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + ‖(1 / 2 : ℂ) + t * I‖⁻¹) *
        Real.sqrt ‖(1 / 2 : ℂ) + t * I‖ := by
  have h := half_line_real_cutoff_bound (original_cutoff_positive t) t
  let r := ‖(1 / 2 : ℂ) + t * I‖
  have hr : 0 < r := by dsimp [r]; linarith [(half_line_norm_geometry t).1]
  have hs := Real.sq_sqrt hr.le
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have h20 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he : 2 * Real.sqrt (r / 2) + r / Real.sqrt (r / 2) +
      Real.sqrt (r / 2) / r + 1 / (2 * Real.sqrt (r / 2)) =
        Real.sqrt 2 * (2 + r⁻¹) * Real.sqrt r := by
    rw [Real.sqrt_div hr.le]
    field_simp
    rw [hs, h2]
    ring
  exact h.trans_eq he

theorem printed_envelope_mono {r R : ℝ} (hr : 1 / 2 ≤ r) (hR : r ≤ R) :
    (2 + r⁻¹) * Real.sqrt r ≤ (2 + R⁻¹) * Real.sqrt R := by
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := hr0.trans_le hR
  have ha := Real.sq_sqrt hr0.le
  have hb := Real.sq_sqrt hR0.le
  have ha0 := Real.sqrt_pos.mpr hr0
  have hb0 := Real.sqrt_pos.mpr hR0
  have hab := Real.sqrt_le_sqrt hR
  have hp : 1 / 2 ≤ Real.sqrt r * Real.sqrt R := by
    nlinarith [mul_le_mul_of_nonneg_left hab ha0.le]
  have he (x : ℝ) (hx : 0 < x) :
      (2 + x⁻¹) * Real.sqrt x = 2 * Real.sqrt x + 1 / Real.sqrt x := by
    have hh := Real.sq_sqrt hx.le
    have hh0 := (Real.sqrt_pos.mpr hx).ne'
    field_simp
    nlinarith
  rw [he r hr0, he R hR0]
  apply (mul_le_mul_iff_of_pos_right (mul_pos ha0 hb0)).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 2 * Real.sqrt r * Real.sqrt R - 1 by linarith)]

theorem equation_3_36 (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      Real.sqrt 2 * (2 + (1 / 2 + |t|)⁻¹) * Real.sqrt (1 / 2 + |t|) := by
  obtain ⟨hr, _, hR⟩ := half_line_norm_geometry t
  have h := mul_le_mul_of_nonneg_left (printed_envelope_mono hr hR) (Real.sqrt_nonneg 2)
  exact (equation_3_36_at_original_cutoff t).trans (by simpa only [mul_assoc] using h)

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.Critical336
