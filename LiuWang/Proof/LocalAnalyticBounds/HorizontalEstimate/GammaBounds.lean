import LiuWang.Proof.LocalAnalyticBounds.ReferenceBounds
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLeftLineLogDerivative

/-!
# 水平条带上的显式伽马因子界

直接消费已证 digamma 有限余项。偶字符先递推一次，故覆盖实部
`[-1/2, 2]`，不把正实部公式误用于左半条带。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate

theorem norm_digamma_le_explicit {z : Complex}
    (hlo : (1 : Real) / 4 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖Complex.digamma z‖ ≤ 8 * Real.log (|z.im| + 2) + 13 := by
  let M : Nat := ⌈|z.im|⌉₊ + 1
  have hM : 1 ≤ M := Nat.le_add_left 1 _
  have hMpos : (0 : Real) < M := by exact_mod_cast (by omega : 0 < M)
  have hMlo : |z.im| + 1 ≤ (M : Real) := by
    dsimp [M]
    push_cast
    linarith [Nat.le_ceil |z.im|]
  have hMhi : (M : Real) ≤ |z.im| + 2 := by
    dsimp [M]
    push_cast
    linarith [Nat.ceil_lt_add_one (abs_nonneg z.im)]
  have hz : ‖z - 1‖ ≤ (M : Real) := by
    have he := Complex.norm_le_abs_re_add_abs_im (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero] at he
    have hr : |z.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have herr : ‖Complex.digamma z - digammaApprox z M‖ ≤ 4 := by
    have h := norm_digamma_sub_approx_le (by norm_num : (0 : Real) < 1 / 4)
      (by norm_num) hlo hM
    have hd : ‖z - 1‖ / ((1 / 4 : Real) * M) ≤ 4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact h.trans hd
  have hgamma : ‖(Real.eulerMascheroniConstant : Complex)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · linarith [Real.eulerMascheroniConstant_lt_two_thirds]
    · linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hhead : ‖digammaApprox z M‖ ≤
      1 + 8 * ((harmonic M : Rat) : Real) := by
    calc
      ‖digammaApprox z M‖ ≤ ‖-(Real.eulerMascheroniConstant : Complex)‖ +
          ∑ n ∈ Finset.range M, ‖((n : Complex) + 1)⁻¹ - (z + n)⁻¹‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
      _ ≤ 1 + ∑ n ∈ Finset.range M, 8 * ((n : Real) + 1)⁻¹ := by
        apply add_le_add (by simpa using hgamma)
        apply Finset.sum_le_sum
        intro n _
        have h := Complex.norm_inv_add_one_sub_inv_le'
          (by norm_num : (0 : Real) < 1 / 4) (by norm_num) hlo n
        calc
          _ ≤ 2 / ((1 / 4 : Real) * ((n : Real) + 1)) := h
          _ = 8 * ((n : Real) + 1)⁻¹ := by
            simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
            ring
      _ = 1 + 8 * ((harmonic M : Rat) : Real) := by
        rw [← Finset.mul_sum, Complex.sum_inv_natCast_add_one_real]
  have htri := norm_sub_le (Complex.digamma z - digammaApprox z M)
    (-digammaApprox z M)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  have hh := harmonic_le_one_add_log M
  have hl := Real.log_le_log hMpos hMhi
  linarith

theorem norm_logDeriv_gammaFactor_horizontal_explicit
    {q : Nat} (chi : DirichletCharacter Complex q) {s : Complex}
    (hlo : -(1 : Real) / 2 ≤ s.re) (hhi : s.re ≤ 2)
    (him : 2 ≤ |s.im|) :
    ‖logDeriv chi.gammaFactor s‖ ≤ 4 * Real.log (|s.im| + 2) + 9 := by
  have hs : -1 < s.re := by linarith
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at him
  have hpi : ‖(Real.log Real.pi : Complex)‖ ≤ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  have hbound : ∀ z : Complex, (1 : Real) / 4 ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ |s.im| →
      ‖Complex.digamma z‖ ≤ 8 * Real.log (|s.im| + 2) + 13 := by
    intro z hz1 hz2 hzi
    have hd := norm_digamma_le_explicit hz1 hz2
    have hl := Real.log_le_log (by positivity : 0 < |z.im| + 2)
      (by linarith : |z.im| + 2 ≤ |s.im| + 2)
    linarith
  have hcore : ∀ d : Complex, ‖d‖ ≤ 8 * Real.log (|s.im| + 2) + 14 →
      ‖-(Real.log Real.pi : Complex) / 2 + (1 / 2 : Complex) * d‖ ≤
        4 * Real.log (|s.im| + 2) + 9 := by
    intro d hd
    have h := norm_add_le (-(Real.log Real.pi : Complex) / 2)
      ((1 / 2 : Complex) * d)
    simp only [norm_div, norm_neg, norm_mul] at h
    norm_num at h
    simp only [Complex.norm_real, Real.norm_eq_abs] at hpi
    linarith
  rcases chi.even_or_odd with he | ho
  · rw [logDeriv_gammaFactor_of_even_of_neg_one_lt_re_of_ne_zero he hs hs0]
    apply hcore
    have hd := hbound ((s + 2) / 2)
      (by simp only [Complex.div_ofNat_re, Complex.add_re]; norm_num; linarith)
      (by simp only [Complex.div_ofNat_re, Complex.add_re]; norm_num; linarith)
      (by simp [abs_div])
    have hr := Complex.digamma_apply_add_one (s / 2)
      (half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hs hs0)
    rw [show s / 2 + 1 = (s + 2) / 2 by ring] at hr
    have hn : 1 ≤ ‖s / 2‖ := by
      have h := Complex.abs_im_le_norm (s / 2)
      rw [Complex.div_ofNat_im, abs_div] at h
      rw [abs_of_pos (by norm_num : (0 : Real) < 2)] at h
      linarith
    have hi : ‖(s / 2)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hn
    have ht := norm_sub_le (Complex.digamma ((s + 2) / 2)) ((s / 2)⁻¹)
    rw [show Complex.digamma ((s + 2) / 2) - (s / 2)⁻¹ =
      Complex.digamma (s / 2) by rw [hr]; ring] at ht
    linarith
  · rw [logDeriv_gammaFactor_of_odd_of_neg_one_lt_re ho hs]
    apply hcore
    have hd := hbound ((s + 1) / 2)
      (by simp only [Complex.div_ofNat_re, Complex.add_re]; norm_num; linarith)
      (by simp only [Complex.div_ofNat_re, Complex.add_re]; norm_num; linarith)
      (by simp [abs_div])
    linarith

end LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate
