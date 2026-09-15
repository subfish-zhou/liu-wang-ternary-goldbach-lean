import LiuWang.Proof.ChebyshevBound.HighHeight.QuarticZeroFree
import Mathlib.Analysis.Complex.Order

/-!
# 按解析重数求和的实际 ξ 零点尾界

在实点 T 使用 Hadamard 正核，不借助未知常数的零点计数。
对 T≥16，全部 |Im ρ|>T 的 1/(Im ρ)^2 之和至多 (2 log T+2)/T。
-/

set_option autoImplicit false
noncomputable section

open Complex Finset ArithmeticFunction BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.LocalAnalyticBounds
open scoped LSeries.notation ComplexOrder

namespace LiuWang.Proof.ChebyshevBound.HighHeight

theorem digamma_real_le_log {x : ℝ} (hx : 1 ≤ x) :
    (digamma (x : ℂ)).re ≤ Real.log (x + 1) + 2 - Real.eulerMascheroniConstant := by
  let M : ℕ := ⌈x⌉₊
  have hMlo : x ≤ (M : ℝ) := Nat.le_ceil x
  have hM : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := hx.trans hMlo
    exact_mod_cast this
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMhi : (M : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have herr : ‖digamma (x : ℂ) - digammaApprox (x : ℂ) M‖ ≤ 1 := by
    have h := norm_digamma_sub_approx_le (a := 1) (z := (x : ℂ)) (by norm_num) le_rfl
      (by simpa using hx) hM
    have hn : ‖(x : ℂ) - 1‖ ≤ (M : ℝ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    simp only [one_mul] at h
    exact h.trans ((div_le_one hM0).2 hn)
  have hhead : (digammaApprox (x : ℂ) M).re ≤
      -Real.eulerMascheroniConstant + (harmonic M : ℚ) := by
    simp only [digammaApprox, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.re_sum]
    apply add_le_add_right
    rw [← Complex.sum_inv_natCast_add_one_real]
    apply sum_le_sum
    intro n _
    have hn : 0 ≤ ((x : ℂ) + n).re := by simp; positivity
    have hinv : 0 ≤ (((x : ℂ) + n)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg hn (Complex.normSq_nonneg _)
    have hid : (((n : ℂ) + 1)⁻¹).re = ((n : ℝ) + 1)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
        ← Complex.ofReal_inv, Complex.ofReal_re]
    simp only [Complex.sub_re, hid]
    linarith
  have he := (Complex.re_le_norm (digamma (x : ℂ) - digammaApprox (x : ℂ) M)).trans herr
  rw [Complex.sub_re] at he
  linarith [harmonic_le_one_add_log M, Real.log_le_log hM0 hMhi]

theorem zeta_real_logderiv_nonneg {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)]
  have h : (0 : ℂ) ≤ LSeries (↗Λ) (σ : ℂ) := by
    apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    norm_cast
    exact vonMangoldt_nonneg
  exact (Complex.nonneg_iff.mp h).1

theorem xiTerm_sum_real_le {T : ℝ} (hT : 4 ≤ T) :
    (∑' p, xiTerm (T : ℂ) p).re ≤ 1 / (T - 1) + Real.log T / 2 + 1 / 3 := by
  have hD := zeta_real_logderiv_nonneg (by linarith : 1 < T)
  rw [Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum
    (by change 1 < T; linarith)] at hD
  have hd := digamma_real_le_log (x := T / 2 + 1) (by linarith)
  have hlog : Real.log (T / 2 + 1 + 1) ≤ Real.log T :=
    Real.log_le_log (by linarith) (by linarith)
  have hgamma : digamma ((T : ℂ) / 2 + 1) = digamma ((T / 2 + 1 : ℝ) : ℂ) := by
    congr 1; push_cast; rfl
  have hp : (1 / ((T : ℂ) - 1)).re = 1 / (T - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re] at hD
  norm_num only [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_div, zero_mul, sub_zero] at hD
  rw [hp, hgamma] at hD
  simp only [one_div_mul_eq_div] at hD
  change 0 ≤ -(logDeriv riemannXi 0).re - (∑' p, xiTerm (T : ℂ) p).re +
    1 / (T - 1) - Real.log Real.pi / 2 + (digamma ((T / 2 + 1 : ℝ) : ℂ)).re / 2 at hD
  linarith [xi_arch_constant, log_two_ge_two_thirds, log_pi_ge_one]

def xiHeightTail (T : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  if T < |(riemannXiDivisorZeroValue p).im| then
    1 / (riemannXiDivisorZeroValue p).im ^ 2 else 0

theorem xiHeightTail_nonneg (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ xiHeightTail T p := by
  unfold xiHeightTail
  split_ifs <;> positivity

theorem xiHeightTail_le_kernel {T : ℝ} (hT : 2 ≤ T) (p : RiemannXiDivisorZeroIndex) :
    xiHeightTail T p ≤ (2 / (T - 1)) * (xiTerm (T : ℂ) p).re := by
  have hTm : 0 < T - 1 := by linarith
  have hK := xiTerm_re_nonneg (s := (T : ℂ)) (by change 1 ≤ T; linarith) p
  unfold xiHeightTail
  split_ifs with ht
  · obtain ⟨hb0, hb1⟩ := riemannXiDivisorZeroValue_re_mem_Ioo p
    let b := (riemannXiDivisorZeroValue p).re
    let t := (riemannXiDivisorZeroValue p).im
    have htpos : 0 < t ^ 2 := by
      have : 0 < |t| := by change 0 < |(riemannXiDivisorZeroValue p).im|; linarith
      exact sq_pos_of_ne_zero (abs_pos.mp this)
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (by linarith) (abs_nonneg t)).2 ht.le
    have ha : 0 < T - b := by dsimp [b]; linarith
    have ha2 : (T - b) ^ 2 ≤ T ^ 2 := by
      dsimp [b]
      nlinarith
    have hd : 0 < (T - b) ^ 2 + t ^ 2 := by positivity
    have hfirst : (T - 1) / (2 * t ^ 2) ≤ (T - b) / ((T - b) ^ 2 + t ^ 2) := by
      calc
        _ ≤ (T - b) / (2 * t ^ 2) := by gcongr
        _ ≤ _ := div_le_div_of_nonneg_left ha.le hd (by linarith)
    have hkernel : (T - b) / ((T - b) ^ 2 + t ^ 2) ≤ (xiTerm (T : ℂ) p).re := by
      have hp : 0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
        rw [one_div, Complex.inv_re]
        exact div_nonneg hb0.le (Complex.normSq_nonneg _)
      have heq : (1 / ((T : ℂ) - riemannXiDivisorZeroValue p)).re =
          (T - b) / ((T - b) ^ 2 + t ^ 2) := by
        simp [b, t, Complex.inv_re, Complex.normSq_apply, pow_two]
      simp only [xiTerm, Complex.add_re, heq]
      linarith
    have h := mul_le_mul_of_nonneg_left (hfirst.trans hkernel)
      (by positivity : 0 ≤ 2 / (T - 1))
    have heq : (2 / (T - 1)) * ((T - 1) / (2 * t ^ 2)) = 1 / t ^ 2 := by
      field_simp [hTm.ne']
    rwa [heq] at h
  · positivity

theorem xiHeightTail_summable {T : ℝ} (hT : 2 ≤ T) :
    Summable (xiHeightTail T) := by
  have hs := (Complex.reCLM.summable (xiTerm_summable (s := (T : ℂ))
    (by change 1 ≤ T; linarith))).mul_left (2 / (T - 1))
  exact Summable.of_nonneg_of_le (xiHeightTail_nonneg T) (xiHeightTail_le_kernel hT) hs

theorem xiHeightTail_sum_le {T : ℝ} (hT : 16 ≤ T) :
    (∑' p, xiHeightTail T p) ≤ (2 * Real.log T + 2) / T := by
  have hT2 : 2 ≤ T := by linarith
  have hTm : 0 < T - 1 := by linarith
  have hsum := (xiHeightTail_summable hT2).tsum_le_tsum (xiHeightTail_le_kernel hT2)
    ((Complex.reCLM.summable (xiTerm_summable (s := (T : ℂ))
      (by change 1 ≤ T; linarith))).mul_left (2 / (T - 1)))
  rw [tsum_mul_left, ← Complex.re_tsum (xiTerm_summable (s := (T : ℂ))
    (by change 1 ≤ T; linarith))] at hsum
  have hbound := xiTerm_sum_real_le (by linarith : 4 ≤ T)
  have hi : 1 / (T - 1) ≤ 1 / 15 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hK : (∑' p, xiTerm (T : ℂ) p).re ≤ Real.log T / 2 + 1 / 2 := by linarith
  have hc : 2 / (T - 1) ≤ 4 / T := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc
    _ ≤ (2 / (T - 1)) * (Real.log T / 2 + 1 / 2) :=
      hsum.trans (mul_le_mul_of_nonneg_left hK (by positivity))
    _ ≤ (4 / T) * (Real.log T / 2 + 1 / 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem xi_height_inverse_square_le_kernel (p : RiemannXiDivisorZeroIndex) :
    1 / (riemannXiDivisorZeroValue p).im ^ 2 ≤ 2 * (xiTerm 1 p).re := by
    have ht := xi_zero_height_gt_one p
    have ht2 : 1 < (riemannXiDivisorZeroValue p).im ^ 2 := by
      nlinarith [sq_abs (riemannXiDivisorZeroValue p).im]
    have hi := xiTerm_one_re_lower p
    have hdiv : 1 / (riemannXiDivisorZeroValue p).im ^ 2 ≤
        2 / (1 + (riemannXiDivisorZeroValue p).im ^ 2) := by
      apply (div_le_div_iff₀ (by linarith) (by positivity)).2
      linarith
    have : 2 / (1 + (riemannXiDivisorZeroValue p).im ^ 2) ≤ 2 * (xiTerm 1 p).re := by
      simp only [div_eq_mul_inv] at hi ⊢
      linarith
    exact hdiv.trans this

theorem xi_height_inverse_square_summable :
    Summable (fun p : RiemannXiDivisorZeroIndex => 1 / (riemannXiDivisorZeroValue p).im ^ 2) := by
  exact Summable.of_nonneg_of_le (fun _ => by positivity) xi_height_inverse_square_le_kernel
    ((Complex.reCLM.summable (xiTerm_summable (s := 1) (by norm_num))).mul_left 2)

theorem xi_height_inverse_square_sum_le :
    (∑' p : RiemannXiDivisorZeroIndex, 1 / (riemannXiDivisorZeroValue p).im ^ 2) ≤ 2 / 3 := by
  have h := xi_height_inverse_square_summable.tsum_le_tsum xi_height_inverse_square_le_kernel
    ((Complex.reCLM.summable (xiTerm_summable (s := 1) (by norm_num))).mul_left 2)
  rw [tsum_mul_left, ← Complex.re_tsum (xiTerm_summable (s := 1) (by norm_num)),
    xiTerm_sum_one] at h
  norm_num only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h
  have hc := xi_constant_lt_third
  norm_num at h ⊢
  linarith

end LiuWang.Proof.ChebyshevBound.HighHeight
