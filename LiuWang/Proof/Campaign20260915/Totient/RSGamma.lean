import LiuWang.Proof.ChebyshevBound.HighHeight.QuarticZeroFree

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex Finset
open LiuWang.Proof.LocalAnalyticBounds
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.Totient

theorem harmonic_le_log_add_two_thirds {n : ℕ} (hn : 6 ≤ n) :
    (harmonic n : ℝ) ≤ Real.log n + 2 / 3 := by
  have h := (Real.strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', if_neg (show n ≠ 0 by omega)] at h
  linarith

theorem digamma_re_high {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2)
    (ht : 5 ≤ |z.im|) :
    (digamma z).re ≤ Real.log (|z.im| + 2) + 5 / 3 -
      Real.eulerMascheroniConstant := by
  let M : ℕ := ⌈|z.im|⌉₊ + 1
  have hMlo : |z.im| + 1 ≤ (M : ℝ) := by
    dsimp [M]
    push_cast
    linarith [Nat.le_ceil |z.im|]
  have hM : 6 ≤ M := by
    have : (6 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMhi : (M : ℝ) ≤ |z.im| + 2 := by
    dsimp [M]
    push_cast
    linarith [Nat.ceil_lt_add_one (abs_nonneg z.im)]
  have hnorm : ‖z - 1‖ ≤ (M : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero] at h
    have hre : |z.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have herr : ‖digamma z - digammaApprox z M‖ ≤ 1 := by
    have h := norm_digamma_sub_approx_le (a := 1) (by norm_num) le_rfl hlo
      (show 1 ≤ M by omega)
    simp only [one_mul] at h
    exact h.trans ((div_le_one hM0).mpr hnorm)
  have hhead : (digammaApprox z M).re ≤
      -Real.eulerMascheroniConstant + (harmonic M : ℚ) := by
    simp only [digammaApprox, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.re_sum]
    apply add_le_add_right
    rw [← Complex.sum_inv_natCast_add_one_real]
    apply sum_le_sum
    intro n _
    have hn : 0 ≤ (z + n).re := by simp; positivity
    have hinv : 0 ≤ ((z + n)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hn (Complex.normSq_nonneg _)
    have hid : (((n : ℂ) + 1)⁻¹).re = ((n : ℝ) + 1)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
        ← Complex.ofReal_inv, Complex.ofReal_re]
    simp only [Complex.sub_re, hid]
    linarith
  have he := (Complex.re_le_norm (digamma z - digammaApprox z M)).trans herr
  rw [Complex.sub_re] at he
  linarith [harmonic_le_log_add_two_thirds hM, Real.log_le_log hM0 hMhi]

theorem rs_archimedean_high {s : ℂ} (hlo : 1 ≤ s.re) (hhi : s.re ≤ 2)
    (ht : 1000 ≤ |s.im|) :
    -(logDeriv riemannXi 0).re - Real.log Real.pi / 2 +
      (digamma (s / 2 + 1)).re / 2 ≤ Real.log |s.im| / 2 - 1 / 4 := by
  have hd := digamma_re_high (z := s / 2 + 1)
    (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)
    (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)
    (by simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, add_zero,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)
  have ht0 : 0 < |s.im| := by linarith
  have he : |s.im| / 2 + 2 = (|s.im| / 2) * (1 + 4 / |s.im|) := by
    field_simp
    norm_num
  have hl : Real.log (|s.im| / 2 + 2) ≤
      Real.log |s.im| - Real.log 2 + 1 / 250 := by
    rw [he, Real.log_mul (by positivity) (by positivity),
      Real.log_div ht0.ne' (by norm_num)]
    have hb := Real.log_le_sub_one_of_pos (show 0 < 1 + 4 / |s.im| by positivity)
    have hq : 4 / |s.im| ≤ 1 / 250 := by
      apply (div_le_iff₀ ht0).mpr
      linarith
    linarith
  have hp : (109 / 100 : ℝ) ≤ Real.log Real.pi := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) Real.pi_gt_three.le
    linarith [Real.log_three_gt_d9]
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, add_zero,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hd
  rw [xi_arch_constant]
  linarith [log_two_ge_two_thirds]

#print axioms rs_archimedean_high

end LiuWang.Proof.Campaign20260915.Totient
