import LiuWang.Proof.ZeroRegionFamily.Uniform.Consumer

/-! # 真实极点的缩放高度付款 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem poleDifference_le_real_kernel {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    poleDifference sigma t ≤ (sigma-1)/((sigma-1)^2+t^2) := by
  have hn : 0 ≤ (1/((stechkinSigma sigma : ℂ)-1+I*(t : ℂ))).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    linarith [stechkinSigma_ge hs]
  have he : (1/((sigma : ℂ)-1+I*(t : ℂ))).re =
      (sigma-1)/((sigma-1)^2+t^2) := by
    simp [one_div, Complex.inv_re, Complex.normSq_apply, pow_two]
  dsimp [poleDifference]
  rw [he]
  exact sub_le_self _ (mul_nonneg stechkinK_mem.1 hn)

theorem harmonicPole_le_real_kernel {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    harmonicPole chi sigma t ≤ (sigma-1)/((sigma-1)^2+t^2) := by
  unfold harmonicPole
  split_ifs
  · exact poleDifference_le_real_kernel hs t
  · positivity

theorem scaled_pole_paid {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {L A v gamma j : ℝ} (hL : 0 < L) (hA : 0 < A) (hv : 0 ≤ v)
    (ht : v ≤ L*|gamma|) :
    harmonicPole chi (1+A/L) (j*gamma) ≤ L*A/(A^2+j^2*v^2) := by
  have hh := harmonicPole_le_real_kernel chi (sigma := 1+A/L)
    (by linarith [div_pos hA hL]) (j*gamma)
  rw [show 1+A/L-1=A/L by ring] at hh
  have he : (A/L)/((A/L)^2+(j*gamma)^2) =
      L*A/(A^2+j^2*(L*|gamma|)^2) := by
    simp only [mul_pow, sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hs : v^2 ≤ (L*|gamma|)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg j)]

theorem log_large_implies_ten {x : ℝ} (hp : 0 < x) (hx : 160 ≤ Real.log x) : 10 ≤ x := by
  by_contra h
  have hh := Real.log_le_log hp (le_of_not_ge h)
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
  linarith

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
