import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.Sources

/-! # 偏心选中反射对：保留实际裸核的负修正，不作错误中心替换 -/

set_option autoImplicit false
noncomputable section

open Complex
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem positive_kernel_le_inverse {a v : ℝ} (ha : 0 < a) :
    a/(a^2+v^2) ≤ 1/a := by
  apply (div_le_div_iff₀ (by positivity) ha).mpr
  nlinarith [sq_nonneg v]

theorem paired_offset_lower {sigma beta v : ℝ} (hs : 1 < sigma)
    (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    (sigma-beta)/((sigma-beta)^2+v^2)-v^2/(sigma-1+beta)^3 ≤
      (sigma-beta)/((sigma-beta)^2+v^2)+(sigma-1+beta)/((sigma-1+beta)^2+v^2)-
        stechkinK*((stechkinSigma sigma-beta)/((stechkinSigma sigma-beta)^2+v^2)+
          (stechkinSigma sigma-1+beta)/((stechkinSigma sigma-1+beta)^2+v^2)) := by
  have hge := stechkinSigma_ge hs
  have ha : 0 < sigma-1+beta := by linarith [hb.1]
  have hb0 : 0 < stechkinSigma sigma-beta := by linarith [hb.2]
  have hc0 : 0 < stechkinSigma sigma-1+beta := by linarith [hb.1]
  have hlow : 1/(sigma-1+beta)-v^2/(sigma-1+beta)^3 ≤
      (sigma-1+beta)/((sigma-1+beta)^2+v^2) := by
    have he : 1/(sigma-1+beta)-
        (sigma-1+beta)/((sigma-1+beta)^2+v^2) =
          v^2/((sigma-1+beta)*((sigma-1+beta)^2+v^2)) := by field_simp; ring
    have hd : (sigma-1+beta)^3 ≤ (sigma-1+beta)*((sigma-1+beta)^2+v^2) := by
      nlinarith [mul_nonneg ha.le (sq_nonneg v)]
    have hh := div_le_div_of_nonneg_left (sq_nonneg v) (pow_pos ha 3) hd
    rw [← he] at hh
    linarith
  have hk := mul_le_mul_of_nonneg_left
    (add_le_add (positive_kernel_le_inverse (v := v) hb0) (positive_kernel_le_inverse (v := v) hc0))
    stechkinK_mem.1
  have hc := selected_reflected_scalar hs hb
  linarith

theorem selected_pair_offset_lower {sigma : ℝ} (hs : 1 < sigma) (t : ℝ)
    {rho : ℂ} (hr : rho.re ∈ Set.Icc (0 : ℝ) 1) :
    (sigma-rho.re)/((sigma-rho.re)^2+(t-rho.im)^2)-
      (t-rho.im)^2/(sigma-1+rho.re)^3 ≤
        dampedZeroKernel sigma t rho+dampedZeroKernel sigma t (1-(starRingEnd ℂ) rho) := by
  have hh := paired_offset_lower (v := t-rho.im) hs hr
  convert hh using 1
  simp [dampedZeroKernel, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

theorem primitive_actual_offset_bound {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+
      (sigma-rho.re)/((sigma-rho.re)^2+(t-rho.im)^2) ≤
        stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+
          4/15+(t-rho.im)^2/(sigma-1+rho.re)^3 := by
  have hb : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hsel := stechkin_actual_zero_selected hc hp hr hz hs t
  have hpair := selected_pair_offset_lower hs t ⟨by linarith, hb.le⟩
  have hg := gammaDifference_le_four_fifteenths chi hs hs1 t
  dsimp [gammaDifferenceAt, stechkinConductorCoeff] at hg ⊢
  linarith

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
