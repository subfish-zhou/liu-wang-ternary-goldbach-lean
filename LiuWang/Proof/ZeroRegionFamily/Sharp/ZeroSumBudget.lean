import LiuWang.Proof.ZeroRegionFamily.Sharp.HighNonreal

/-! # 保实际全重数有号零点和的差分母式，不先删掉零点费用 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

def primitiveZeroSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma t : ℝ) : ℝ :=
  ∑' p : SymmetricCompletedZeroIndex chi,
    dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p)

def zetaZeroSum (sigma t : ℝ) : ℝ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)

theorem primitive_full_zero_sum_bound {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+primitiveZeroSum chi sigma t ≤
      stechkinConductorCoeff*(Real.log q+Real.log (max 1 |t|)-Real.log Real.pi)+4/15 := by
  have hi := damped_kernel_identity hc hp hs (hs.trans_le (stechkinSigma_ge hs)) stechkinK t
  have hg := gammaDifference_le_four_fifteenths chi hs hs1 t
  dsimp [primitiveZeroSum, dampedZeroKernel, gammaDifferenceAt, stechkinConductorCoeff] at *
  nlinarith

theorem imprimitive_full_zero_sum_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+
        @primitiveZeroSum chi.conductor ⟨chi.conductor_ne_zero⟩ chi.primitiveCharacter sigma t ≤
      stechkinConductorCoeff*(Real.log chi.conductor+Real.log (max 1 |t|)-Real.log Real.pi)+
        4/15+badPrimeCost chi sigma := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hh := primitive_full_zero_sum_bound hpr chi.primitiveCharacter_isPrimitive hs hs1 t
  have he := norm_level_difference_le chi hc hs t
  have hr := (neg_le_abs
    (logDeriv (levelCorrection chi) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (levelCorrection chi) ((stechkinSigma sigma : ℂ)+Complex.I*t)).re).trans
    (Complex.abs_re_le_norm _)
  unfold dampedLogDeriv at *
  rw [logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [Complex.mul_re] using hs.le),
    logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le)]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at *
  linarith

theorem zeta_full_zero_sum_identity {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    zetaDamped sigma t+zetaZeroSum sigma t =
      poleDifference sigma t+shiftedGammaDifference sigma t := by
  have hi := zeta_damped_identity hs t
  have h0 : 1 ≤ ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs.le
  have h1 : 1 ≤ ((stechkinSigma sigma : ℂ)+Complex.I*t).re := by
    simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le
  have hf := (xi_raw_summable h0).sub ((xi_raw_summable h1).mul_left stechkinK)
  change Summable (fun p : RiemannXiDivisorZeroIndex =>
    dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)) at hf
  have hid : xiDampedTerm sigma t =
      fun p => dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)+
        (1-stechkinK)*(1/riemannXiDivisorZeroValue p).re := by
    funext p
    simp only [xiDampedTerm, xiTerm, Complex.add_re, dampedZeroKernel]
    ring
  simp only [hid] at hi
  rw [hf.tsum_add (xi_inv_re_summable.mul_left (1-stechkinK)),
    tsum_mul_left, xi_inv_re_sum] at hi
  dsimp [zetaZeroSum]
  linarith

theorem principal_full_zero_sum_bound {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t+
        zetaZeroSum sigma t ≤
      poleDifference sigma t+stechkinConductorCoeff*(Real.log (max 1 |t|)-Real.log Real.pi)+
        23/40-11*stechkinK/30+principalPrimeCost q sigma := by
  have he := principal_damped_euler_bound (q := q) hs t
  have hz := zeta_full_zero_sum_identity hs t
  have hg := shiftedGamma_all_height hs hs1 t
  change dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t ≤
    zetaDamped sigma t+principalPrimeCost q sigma at he
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
