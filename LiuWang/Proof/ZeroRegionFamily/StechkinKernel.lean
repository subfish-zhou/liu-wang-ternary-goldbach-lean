import LiuWang.Proof.ZeroRegionFamily.StechkinPair
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorReflection

/-! # 由保解析重数的真实反射对合支付全部Stechkin差核 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ZeroRegionFamily

def dampedZeroKernel (sigma t : ℝ) (rho : ℂ) : ℝ :=
  (1/((sigma : ℂ)+Complex.I*t-rho)).re-
    stechkinK*(1/((stechkinSigma sigma : ℂ)+Complex.I*t-rho)).re

theorem dampedZeroKernel_pair_nonneg {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) {rho : ℂ} (hr : rho.re ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ dampedZeroKernel sigma t rho+dampedZeroKernel sigma t (1-(starRingEnd ℂ) rho) := by
  have h := stechkin_paired_kernel_nonneg (t := t-rho.im) hs hr
  convert h using 1
  simp [dampedZeroKernel, one_div, Complex.inv_re, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

theorem summable_dampedZeroKernel {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    Summable (fun p : SymmetricCompletedZeroIndex chi =>
      dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p)) := by
  have h0 : 1 < ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs
  have h1 : 1 < ((stechkinSigma sigma : ℂ)+Complex.I*t).re := by
    simpa [Complex.mul_re] using hs.trans_le (stechkinSigma_ge hs)
  exact (summable_symmetricCompletedLFunction_zeroKernel_re hc hp h0).sub
    ((summable_symmetricCompletedLFunction_zeroKernel_re hc hp h1).mul_left stechkinK)

theorem damped_zero_sum_nonneg {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    0 ≤ ∑' p : SymmetricCompletedZeroIndex chi,
      dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let f := fun p : SymmetricCompletedZeroIndex chi =>
    dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p)
  let e := symmetricCompletedZeroReflectionEquiv hc hp
  have hsum : Summable f := summable_dampedZeroKernel hc hp hs t
  have hcomp : Summable (fun p => f (e p)) := e.summable_iff.mpr hsum
  have hnon : 0 ≤ ∑' p, (f p+f (e p)) := by
    apply tsum_nonneg
    intro p
    dsimp [f, e]
    rw [symmetricCompletedZeroReflectionEquiv_val]
    exact dampedZeroKernel_pair_nonneg hs t
      ⟨(symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp p).1.le,
        (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp p).2.le⟩
  rw [hsum.tsum_add hcomp, e.tsum_eq f] at hnon
  change 0 ≤ ∑' p, f p
  linarith

theorem stechkin_without_zeros {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      (1-stechkinK)*Real.log q/2+
      (logDeriv chi.gammaFactor ((sigma : ℂ)+Complex.I*t)).re-
      stechkinK*(logDeriv chi.gammaFactor ((stechkinSigma sigma : ℂ)+Complex.I*t)).re := by
  have hi := damped_kernel_identity hc hp hs (hs.trans_le (stechkinSigma_ge hs)) stechkinK t
  have hn := damped_zero_sum_nonneg hc hp hs t
  dsimp [dampedZeroKernel] at hn
  linarith

theorem damped_selected_pair_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) (p : SymmetricCompletedZeroIndex chi)
    (hhigh : 1/2 < (Complex.Hadamard.divisorZeroIndex₀_val p).re) :
    dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p)+
      dampedZeroKernel sigma t (1-(starRingEnd ℂ) (Complex.Hadamard.divisorZeroIndex₀_val p)) ≤
      ∑' j : SymmetricCompletedZeroIndex chi,
        dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val j) := by
  classical
  let f := fun j : SymmetricCompletedZeroIndex chi =>
    dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val j)
  let e := symmetricCompletedZeroReflectionEquiv hc hp
  let g := fun j => f j+f (e j)
  have hsum : Summable f := summable_dampedZeroKernel hc hp hs t
  have hcomp : Summable (fun j => f (e j)) := e.summable_iff.mpr hsum
  have hnon : ∀ j, 0 ≤ g j := by
    intro j
    dsimp [g, f, e]
    rw [symmetricCompletedZeroReflectionEquiv_val]
    exact dampedZeroKernel_pair_nonneg hs t
      ⟨(symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp j).1.le,
        (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hc hp j).2.le⟩
  have hne : p ≠ e p := by
    intro he
    have hv := congrArg Complex.Hadamard.divisorZeroIndex₀_val he
    dsimp [e] at hv
    rw [symmetricCompletedZeroReflectionEquiv_val] at hv
    have hh := congrArg Complex.re hv
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hh
    linarith
  have hge : g (e p)=g p := by
    have hee : e (e p)=p := symmetricCompletedZeroReflection_involutive hc hp p
    dsimp [g]
    rw [hee]
    ring
  have hselected := (hsum.add hcomp).sum_le_tsum {p, e p} (fun j _ => hnon j)
  change ∑ j ∈ ({p, e p} : Finset _), g j ≤ ∑' j, g j at hselected
  rw [Finset.sum_pair hne, hge] at hselected
  have htotal : (∑' j, g j)=2*∑' j, f j := by
    dsimp [g]
    rw [hsum.tsum_add hcomp, e.tsum_eq f]
    ring
  rw [htotal] at hselected
  have hpval : g p =
      dampedZeroKernel sigma t (Complex.Hadamard.divisorZeroIndex₀_val p)+
      dampedZeroKernel sigma t (1-(starRingEnd ℂ) (Complex.Hadamard.divisorZeroIndex₀_val p)) := by
    dsimp [g, f, e]
    rw [symmetricCompletedZeroReflectionEquiv_val]
  rw [hpval] at hselected
  change _ ≤ ∑' j, f j
  linarith

end LiuWang.Proof.ZeroRegionFamily
