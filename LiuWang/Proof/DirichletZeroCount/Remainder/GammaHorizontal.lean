import LiuWang.Proof.DirichletZeroCount.Remainder.DigammaImaginary
import LiuWang.Proof.DirichletZeroCount.Remainder.HorizontalFee

/-! # Uniform actual Gamma phase differences on a common horizontal line -/

set_option autoImplicit false
noncomputable section
open Complex
open LiuWang.Proof.Interfaces (Character)
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.DirichletZeroCount.Remainder

theorem digamma_im_nonneg {z : ℂ} (hz : 0 < z.re) (ht : 0 ≤ z.im) :
    0 ≤ (digamma z).im := by
  rw [← (digamma_im_hasSum hz).tsum_eq]
  exact tsum_nonneg (fun n => div_nonneg ht (by positivity))

theorem digamma_im_nonpos {z : ℂ} (hz : 0 < z.re) (ht : z.im ≤ 0) :
    (digamma z).im ≤ 0 := by
  rw [← (digamma_im_hasSum hz).tsum_eq]
  exact tsum_nonpos (fun n => div_nonpos_of_nonpos_of_nonneg ht (by positivity))

theorem digamma_im_difference_le_quarter {z w : ℂ}
    (hz : 1 / 4 ≤ z.re) (hw : 1 / 4 ≤ w.re) (ht : z.im = w.im) :
    |(digamma z).im - (digamma w).im| ≤ 2 + Real.pi / 2 := by
  have hzb := abs_le.mp (digamma_im_abs_le_quarter hz)
  have hwb := abs_le.mp (digamma_im_abs_le_quarter hw)
  have hz0 : 0 < z.re := by linarith
  have hw0 : 0 < w.re := by linarith
  rcases le_total 0 z.im with hpos | hneg
  · have hzn := digamma_im_nonneg hz0 hpos
    have hwn := digamma_im_nonneg hw0 (ht ▸ hpos)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hzn := digamma_im_nonpos hz0 hneg
    have hwn := digamma_im_nonpos hw0 (ht ▸ hneg)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gammaFactor_im_difference_le {q : ℕ} (chi : Character q) {s w : ℂ}
    (hs : 1 / 2 ≤ s.re) (hw : 1 / 2 ≤ w.re) (ht : s.im = w.im) :
    |(logDeriv chi.gammaFactor s).im - (logDeriv chi.gammaFactor w).im| ≤
      1 + Real.pi / 4 := by
  rcases chi.even_or_odd with he | ho
  · rw [logDeriv_gammaFactor_of_even he (by linarith),
      logDeriv_gammaFactor_of_even he (by linarith)]
    have hd := digamma_im_difference_le_quarter (z := s / 2) (w := w / 2)
      (by simp; linarith) (by simp; linarith) (by simp [ht])
    have heq :
        (-↑(Real.log Real.pi) / 2 + 1 / 2 * digamma (s / 2) : ℂ).im -
        (-↑(Real.log Real.pi) / 2 + 1 / 2 * digamma (w / 2) : ℂ).im =
          ((digamma (s / 2)).im - (digamma (w / 2)).im) / 2 := by
      simp
      ring
    rw [heq, abs_div]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · rw [logDeriv_gammaFactor_of_odd ho (by linarith),
      logDeriv_gammaFactor_of_odd ho (by linarith)]
    have hd := digamma_im_difference_le_quarter (z := (s + 1) / 2) (w := (w + 1) / 2)
      (by simp; linarith) (by simp; linarith) (by simp [ht])
    have heq :
        (-↑(Real.log Real.pi) / 2 + 1 / 2 * digamma ((s + 1) / 2) : ℂ).im -
        (-↑(Real.log Real.pi) / 2 + 1 / 2 * digamma ((w + 1) / 2) : ℂ).im =
          ((digamma ((s + 1) / 2)).im - (digamma ((w + 1) / 2)).im) / 2 := by
      simp
      ring
    rw [heq, abs_div]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

end LiuWang.Proof.DirichletZeroCount.Remainder
