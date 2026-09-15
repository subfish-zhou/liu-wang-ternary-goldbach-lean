import LiuWang.Proof.NearOneDensity.ReflectedFamily

set_option autoImplicit false
noncomputable section

open Complex
open scoped ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity

theorem reciprocal_real_part_le {u d : ℝ} (hu : 0 < u) :
    u / (u ^ 2 + d ^ 2) ≤ 1 / u := by
  rw [div_le_div_iff₀ (by positivity) hu]
  nlinarith [sq_nonneg d]

theorem reciprocal_real_part_loss {u d : ℝ} (hu : 1 / 2 ≤ u) :
    1 / u - 8 * d ^ 2 ≤ u / (u ^ 2 + d ^ 2) := by
  have hp : 0 < u := by linarith
  have hden : 0 < u ^ 2 + d ^ 2 := by positivity
  have hu2 : 1 / 4 ≤ u ^ 2 := by nlinarith
  have hu3 : 1 / 8 ≤ u * u ^ 2 :=
    (by nlinarith [mul_le_mul hu hu2 (by norm_num : (0 : ℝ) ≤ 1 / 4) hp.le])
  have hprod := mul_le_mul_of_nonneg_right hu3 (sq_nonneg d)
  apply (le_div_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ hp).mp
  field_simp
  nlinarith [mul_nonneg hp.le (sq_nonneg (d ^ 2))]

theorem damped_pair_local_lower {σ : ℝ} (hσ : 1 < σ) {ρ : ℂ}
    (hρ : ρ.re ∈ Set.Icc (1 / 2 : ℝ) 1) (t : ℝ) :
    (σ - ρ.re) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2) - 8 * (t - ρ.im) ^ 2 ≤
      dampedZeroKernel σ t ρ + dampedZeroKernel σ t (1 - conj ρ) := by
  have hge := stechkinSigma_ge hσ
  have hscalar := selected_reflected_scalar hσ
    (show ρ.re ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith [hρ.1], hρ.2⟩)
  have hu := reciprocal_real_part_loss (d := t - ρ.im)
    (show 1 / 2 ≤ σ - 1 + ρ.re by linarith [hρ.1])
  have h1 := reciprocal_real_part_le (d := t - ρ.im)
    (show 0 < stechkinSigma σ - ρ.re by linarith [hρ.2])
  have h2 := reciprocal_real_part_le (d := t - ρ.im)
    (show 0 < stechkinSigma σ - 1 + ρ.re by linarith [hρ.1])
  have hm := mul_le_mul_of_nonneg_left (add_le_add h1 h2) stechkinK_mem.1
  simp only [dampedZeroKernel, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im, mul_zero,
    zero_mul, one_mul, sub_zero, add_zero, zero_add, sub_neg_eq_add]
  simp only [← sq]
  have hev : σ - (1 - ρ.re) = σ - 1 + ρ.re := by ring
  have hev' : stechkinSigma σ - (1 - ρ.re) = stechkinSigma σ - 1 + ρ.re := by ring
  rw [hev, hev']
  simp only [one_div] at hscalar hu hm
  linarith

theorem cauchy_kernel_interval_lower {u U d B : ℝ}
    (hu : 0 < u) (huU : u ≤ U) (hB : 0 ≤ B) (hBu : B ≤ u) (hd : |d| ≤ B) :
    U / (U ^ 2 + B ^ 2) ≤ u / (u ^ 2 + d ^ 2) := by
  have hU : 0 < U := hu.trans_le huU
  have hd2 : d ^ 2 ≤ B ^ 2 := by
    have h := mul_le_mul hd hd (abs_nonneg d) hB
    nlinarith [sq_abs d]
  have hh : B ^ 2 ≤ u * U := by nlinarith [mul_le_mul hBu hBu hB hu.le]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hprod := mul_nonneg (sub_nonneg.mpr huU) (sub_nonneg.mpr hh)
  nlinarith [mul_le_mul_of_nonneg_left hd2 hU.le]

theorem scaled_window_pair_lower {a b lam L σ t : ℝ} {ρ : ℂ}
    (hL : 25 ≤ L) (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a)
    (hbmax : b ≤ 2.04) (hσ : σ = 1 + a / L)
    (hρ : ρ.re ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hre : 1 - lam / L ≤ ρ.re) (ht : |t - ρ.im| ≤ b / L) :
    L * ((a + lam) / ((a + lam) ^ 2 + b ^ 2)) - 3 / 50 ≤
      dampedZeroKernel σ t ρ + dampedZeroKernel σ t (1 - conj ρ) := by
  have hL0 : 0 < L := by linarith
  have hσ0 : 1 < σ := by rw [hσ]; linarith [div_pos ha hL0]
  have hu : 0 < σ - ρ.re := by linarith [hρ.2]
  have hupper : σ - ρ.re ≤ (a + lam) / L := by rw [hσ]; rw [add_div]; linarith
  have hBu : b / L ≤ σ - ρ.re := by
    have h := (div_le_div_iff_of_pos_right hL0).mpr hba.le
    rw [hσ]
    linarith [hρ.2]
  have hmain := cauchy_kernel_interval_lower hu hupper (div_nonneg hb hL0.le) hBu ht
  have hsmall : b / L ≤ 2.04 / 25 :=
    div_le_div₀ (by norm_num) hbmax (by norm_num) hL
  have hsq : (t - ρ.im) ^ 2 ≤ (2.04 / 25 : ℝ) ^ 2 := by
    have hbound := ht.trans hsmall
    have h := mul_le_mul hbound hbound (abs_nonneg (t - ρ.im)) (by norm_num : (0 : ℝ) ≤ 2.04 / 25)
    nlinarith [sq_abs (t - ρ.im)]
  have he : ((a + lam) / L) / (((a + lam) / L) ^ 2 + (b / L) ^ 2) =
      L * ((a + lam) / ((a + lam) ^ 2 + b ^ 2)) := by
    field_simp
  rw [he] at hmain
  linarith [damped_pair_local_lower hσ0 hρ t]

end LiuWang.Proof.NearOneDensity
