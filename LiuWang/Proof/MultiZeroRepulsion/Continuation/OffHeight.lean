import LiuWang.Proof.MultiZeroRepulsion.Continuation.PrimitivePair

/-! Quantitative off-height kernels retained to pay principal-product poles. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

def realKernel (a u : ℝ) : ℝ := a / (a ^ 2 + u ^ 2)

theorem realKernel_nonneg {a : ℝ} (ha : 0 ≤ a) (u : ℝ) : 0 ≤ realKernel a u :=
  div_nonneg ha (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem realKernel_le_inverse {a : ℝ} (ha : 0 < a) (u : ℝ) :
    realKernel a u ≤ 1 / a := by
  dsimp [realKernel]
  apply (div_le_div_iff₀ (by nlinarith [sq_nonneg u]) ha).mpr
  nlinarith [sq_nonneg u]

theorem realKernel_half_pole {a d u : ℝ} (hd : 0 < d) (ha : d ≤ a) (ha2 : a ≤ 2 * d) :
    realKernel d u / 2 ≤ realKernel a u := by
  have ha0 : 0 < a := hd.trans_le ha
  have hmul : 0 ≤ a * d * (2 * d - a) := mul_nonneg (by positivity) (by linarith)
  have hsq : 0 ≤ (2 * a - d) * u ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  dsimp [realKernel]
  rw [div_div]
  apply (div_le_div_iff₀ (mul_pos (by nlinarith [sq_nonneg u]) (by norm_num))
    (by nlinarith [sq_nonneg u])).mpr
  nlinarith

theorem dampedKernel_eq_realKernel (sigma t : ℝ) (rho : ℂ) :
    dampedZeroKernel sigma t rho = realKernel (sigma - rho.re) (t - rho.im) -
      stechkinK * realKernel (stechkinSigma sigma - rho.re) (t - rho.im) := by
  simp [dampedZeroKernel, realKernel, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, pow_two]

theorem damped_inverse_pair_le {sigma beta : ℝ} (hs : 1 < sigma)
    (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    stechkinK * (1 / (stechkinSigma sigma - beta) +
      1 / (stechkinSigma sigma - 1 + beta)) ≤ 1 / sigma := by
  have hge := stechkinSigma_ge hs
  have hc : 0 < stechkinSigma sigma - beta := by linarith [hb.2]
  have hd : 0 < stechkinSigma sigma - 1 + beta := by linarith [hb.1]
  have he : (stechkinSigma sigma - beta) * (stechkinSigma sigma - 1 + beta) =
      sigma ^ 2 + beta * (1 - beta) := by
    nlinarith [stechkinSigma_equation sigma]
  have hrat := mul_le_mul_of_nonneg_right (stechkin_ratio_sigma hs) (show 0 ≤ sigma by linarith)
  have hpos := mul_nonneg hb.1 (show 0 ≤ 1 - beta by linarith [hb.2])
  rw [div_add_div _ _ hc.ne' hd.ne', ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hc hd) (by linarith)).mpr
  nlinarith

theorem reflectedKernel_lower {sigma : ℝ} (hs : 1 < sigma)
    {rho : ℂ} (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1) (t : ℝ) :
    realKernel (sigma - rho.re) (t - rho.im) - 1 / sigma ≤ reflectedKernel sigma t rho := by
  have hge := stechkinSigma_ge hs
  have hc : 0 < stechkinSigma sigma - rho.re := by linarith [hr.2]
  have hd : 0 < stechkinSigma sigma - 1 + rho.re := by linarith [hr.1]
  have h1 := mul_le_mul_of_nonneg_left (realKernel_le_inverse hc (t - rho.im)) stechkinK_mem.1
  have h2 := mul_le_mul_of_nonneg_left (realKernel_le_inverse hd (t - rho.im)) stechkinK_mem.1
  have hp := realKernel_nonneg (show 0 ≤ sigma - 1 + rho.re by linarith [hr.1]) (t - rho.im)
  have hi := damped_inverse_pair_le hs ⟨hr.1.le, hr.2.le⟩
  unfold reflectedKernel
  rw [dampedKernel_eq_realKernel, dampedKernel_eq_realKernel]
  simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, sub_neg_eq_add, zero_add]
  rw [show sigma - (1 - rho.re) = sigma - 1 + rho.re by ring,
    show stechkinSigma sigma - (1 - rho.re) = stechkinSigma sigma - 1 + rho.re by ring]
  linarith

theorem reflectedKernel_half_pole {sigma : ℝ} (hs : 1 < sigma)
    {rho : ℂ} (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1)
    (hgap : 1 - rho.re ≤ sigma - 1) (t : ℝ) :
    realKernel (sigma - 1) (t - rho.im) / 2 - 1 / sigma ≤ reflectedKernel sigma t rho := by
  have hh := realKernel_half_pole (u := t - rho.im) (by linarith : 0 < sigma - 1)
    (show sigma - 1 ≤ sigma - rho.re by linarith [hr.2])
    (show sigma - rho.re ≤ 2 * (sigma - 1) by linarith)
  linarith [reflectedKernel_lower hs hr t]

theorem poleDifference_le_realKernel {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    poleDifference sigma t ≤ realKernel (sigma - 1) t := by
  have hpos := mul_nonneg stechkinK_mem.1
    (realKernel_nonneg (show 0 ≤ stechkinSigma sigma - 1 by linarith [stechkinSigma_ge hs]) t)
  have he : poleDifference sigma t =
      realKernel (sigma - 1) t - stechkinK * realKernel (stechkinSigma sigma - 1) t := by
    simp [poleDifference, realKernel, one_div, Complex.inv_re, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, pow_two]
  rw [he]
  linarith

end LiuWang.Proof.MultiZeroRepulsion.Continuation
