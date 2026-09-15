import LiuWang.Proof.ChebyshevBound.HighHeight.XiKernel
import LiuWang.Proof.LocalAnalyticBounds.DigammaRemainder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # 实部 Γ 界：保留主项系数 1，不用复范数界中的系数 8。 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open LiuWang.Proof.LocalAnalyticBounds

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem log_two_ge_two_thirds : (2 / 3 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem log_pi_ge_one : (1 : ℝ) ≤ Real.log Real.pi := by
  apply (Real.le_log_iff_exp_le Real.pi_pos).2
  exact Real.exp_one_lt_d9.le.trans (by linarith [Real.pi_gt_three])

theorem digamma_re_le_log_add {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) :
    (Complex.digamma z).re ≤ Real.log (|z.im| + 2) + 2 -
      Real.eulerMascheroniConstant := by
  let M : ℕ := ⌈|z.im|⌉₊ + 1
  have hM : 1 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMlo : |z.im| + 1 ≤ (M : ℝ) := by
    dsimp [M]
    push_cast
    linarith [Nat.le_ceil |z.im|]
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
  have herr : ‖Complex.digamma z - digammaApprox z M‖ ≤ 1 := by
    have h := norm_digamma_sub_approx_le (a := 1) (by norm_num) le_rfl hlo hM
    norm_num only [one_mul] at h
    exact h.trans ((div_le_one hM0).2 hnorm)
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
    simp only [Complex.sub_re]
    have hid : (((n : ℂ) + 1)⁻¹).re = ((n : ℝ) + 1)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
        ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [hid]
    linarith
  have he := (Complex.re_le_norm (Complex.digamma z - digammaApprox z M)).trans herr
  rw [Complex.sub_re] at he
  have hh := harmonic_le_one_add_log M
  have hl := Real.log_le_log hM0 hMhi
  linarith

theorem digamma_real_le_one_sub_gamma {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    (Complex.digamma (x : ℂ)).re ≤ 1 - Real.eulerMascheroniConstant := by
  have hp (z : ℂ) (hz : 0 < z.re) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hx : 0 < (x : ℂ).re := by simpa using (show 0 < x by linarith)
  have hsum := Complex.hasSum_digamma (hp (x : ℂ) hx)
  have htwo := Complex.hasSum_digamma (hp (2 : ℂ) (by norm_num))
  have hterm (n : ℕ) :
      (((n : ℂ) + 1)⁻¹ - ((x : ℂ) + n)⁻¹).re ≤
        (((n : ℂ) + 1)⁻¹ - ((2 : ℂ) + n)⁻¹).re := by
    simp only [Complex.sub_re]
    apply sub_le_sub_left
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hinv : (2 + (n : ℝ))⁻¹ ≤ (x + (n : ℝ))⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_add, ← Complex.ofReal_inv, Complex.ofReal_re] using hinv
  have hsreal := Complex.hasSum_re hsum
  have htreal := Complex.hasSum_re htwo
  have hle := hsreal.summable.tsum_le_tsum
    (fun n => by simpa only [one_div, add_comm] using hterm n) htreal.summable
  rw [hsreal.tsum_eq, htreal.tsum_eq] at hle
  have hd := Complex.digamma_apply_add_one (1 : ℂ) (by
    intro n h
    have hr := congrArg Complex.re h
    simp at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith)
  norm_num [Complex.digamma_one] at hd
  rw [hd] at hle
  simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hle
  linarith

theorem archimedean_re_le {s : ℂ} (hlo : 1 ≤ s.re) (hhi : s.re ≤ 2) :
    -(logDeriv riemannXi 0).re - Real.log Real.pi / 2 +
      (Complex.digamma (s / 2 + 1)).re / 2 ≤
        Real.log (|s.im| + 2) / 2 + 1 / 3 := by
  have hd := digamma_re_le_log_add (z := s / 2 + 1)
    (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)
    (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)
  have hlog : Real.log (|(s / 2 + 1).im| + 2) ≤ Real.log (|s.im| + 2) := by
    apply Real.log_le_log (by positivity)
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, add_zero,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg s.im]
  rw [xi_arch_constant]
  linarith [log_two_ge_two_thirds, log_pi_ge_one]

theorem zeta_real_le_pole {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) := by
  have h := zeta_without_zeros_le (s := (σ : ℂ)) (by simpa using hσ)
  have hd := digamma_real_le_one_sub_gamma (x := σ / 2 + 1)
    (by linarith) (by linarith)
  have hconst := xi_arch_constant
  have hgamma : Complex.digamma ((σ : ℂ) / 2 + 1) =
      Complex.digamma ((σ / 2 + 1 : ℝ) : ℂ) := by congr 1; push_cast; rfl
  rw [hgamma] at h
  have hpole : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hpole] at h
  linarith [log_two_ge_two_thirds, log_pi_ge_one]

end LiuWang.Proof.ChebyshevBound.HighHeight
