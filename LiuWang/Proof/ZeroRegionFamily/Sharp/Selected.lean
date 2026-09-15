import LiuWang.Proof.ZeroRegionFamily.Sharp.Principal
import LiuWang.Proof.ZeroRegionFamily.Consumer

/-! # 实际普通L选中零点：反射对直接支付完整的1/(sigma-beta) -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem stechkin_ratio_sigma {sigma : ℝ} (hs : 1 < sigma) :
    stechkinK*(2*stechkinSigma sigma-1) ≤ sigma := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hroot := Real.sq_sqrt (show 0 ≤ 1+4*sigma^2 by positivity)
  have hr := Real.sqrt_nonneg (1+4*sigma^2)
  dsimp [stechkinK, stechkinSigma]
  rw [one_div_mul_eq_div, div_le_iff₀ hp]
  nlinarith [mul_pos (show 0 < sigma by linarith) hp]

theorem selected_reflected_scalar {sigma beta : ℝ} (hs : 1 < sigma)
    (hb : beta ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 1/(sigma-1+beta)-
      stechkinK*(1/(stechkinSigma sigma-beta)+1/(stechkinSigma sigma-1+beta)) := by
  have hge := stechkinSigma_ge hs
  have ha : 0 < stechkinSigma sigma-beta := by linarith [hb.2]
  have hb0 : 0 < stechkinSigma sigma-1+beta := by linarith [hb.1]
  have hc : 0 < sigma-1+beta := by linarith [hb.1]
  have he : (stechkinSigma sigma-beta)*(stechkinSigma sigma-1+beta) =
      sigma^2+beta*(1-beta) := by
    have hh := stechkinSigma_equation sigma
    nlinarith
  have hr := mul_le_mul_of_nonneg_right (stechkin_ratio_sigma hs) hc.le
  have hbound : stechkinK*(2*stechkinSigma sigma-1)*(sigma-1+beta) ≤
      (stechkinSigma sigma-beta)*(stechkinSigma sigma-1+beta) := by
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ 1-beta by linarith [hb.2]) (show 0 ≤ sigma+beta by linarith [hb.1])]
  apply sub_nonneg.mpr
  rw [div_add_div _ _ ha.ne' hb0.ne']
  simp only [one_mul, mul_one]
  rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos ha hb0) hc]
  nlinarith

theorem selected_pair_dominates {sigma : ℝ} (hs : 1 < sigma)
    {rho : ℂ} (hr : rho.re ∈ Set.Ioo (0 : ℝ) 1) :
    1/(sigma-rho.re) ≤ dampedZeroKernel sigma rho.im rho+
      dampedZeroKernel sigma rho.im (1-(starRingEnd ℂ) rho) := by
  have hscalar := selected_reflected_scalar hs ⟨hr.1.le, hr.2.le⟩
  have hge := stechkinSigma_ge hs
  have he (u : ℝ) (hu : 1 < u) :
      (1/((u : ℂ)+Complex.I*rho.im-rho)).re=1/(u-rho.re) ∧
      (1/((u : ℂ)+Complex.I*rho.im-(1-(starRingEnd ℂ) rho))).re=1/(u-1+rho.re) := by
    have h0 : u-rho.re ≠ 0 := by linarith [hr.2]
    have h1 : u-1+rho.re ≠ 0 := by linarith [hr.1]
    constructor
    · simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    · simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
  simp only [dampedZeroKernel]
  rw [(he sigma hs).1, (he sigma hs).2, (he _ (hs.trans_le hge)).1, (he _ (hs.trans_le hge)).2]
  linarith

theorem primitive_actual_selected_bound {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {rho : ℂ}
    (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK rho.im+1/(sigma-rho.re) ≤
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |rho.im|)-Real.log Real.pi)+4/15 := by
  have hbeta : rho.re < 1 := by
    by_contra h
    exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) (le_of_not_gt h) hz
  have hsel := stechkin_actual_zero_selected hc hp hr hz hs rho.im
  have hpair := selected_pair_dominates hs ⟨by linarith, hbeta⟩
  have hg := gammaDifference_le_four_fifteenths chi hs hs1 rho.im
  dsimp [gammaDifferenceAt, stechkinConductorCoeff] at hg ⊢
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
