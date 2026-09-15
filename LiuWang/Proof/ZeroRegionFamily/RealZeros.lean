import LiuWang.Proof.ZeroRegionFamily.RealKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLFunctionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndexOfLFunctionZero
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionOrder
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveLFunctionZero
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-! # 普通 L 的实际实零点唯一与单性：显式宽度 1/(3 log q) -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ZeroRegionFamily

theorem log_level_gt_one {q : ℕ} (hq : 3 ≤ q) : 1 < Real.log q := by
  apply (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < q by omega))).mpr
  have hh : (3 : ℝ) ≤ q := by exact_mod_cast hq
  linarith [Real.exp_one_lt_d9]

theorem real_pair_contradiction {L beta gamma : ℝ} (hL : 1 < L)
    (hb : beta < 1) (hg : gamma < 1)
    (hbgap : 1 - beta < 1 / (3*L)) (hggap : 1 - gamma < 1 / (3*L))
    (hbound : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      1/(sigma-beta)+1/(sigma-gamma) ≤ 1/(sigma-1)+L/2) : False := by
  have hL0 : 0 < L := by linarith
  have hLi : 0 < 1/L := by positivity
  have hLi1 : 1/L ≤ 1 := (div_le_one hL0).mpr hL.le
  have h := hbound (1+1/L) (by linarith) (by linarith)
  have hterm (b : ℝ) (hb1 : b < 1) (hbGap : 1-b < 1/(3*L)) :
      3*L/4 < 1/(1+1/L-b) := by
    have hgap := (lt_div_iff₀ (show 0 < 3*L by positivity)).mp hbGap
    apply (lt_div_iff₀ (show 0 < 1+1/L-b by linarith)).mpr
    have he : L*(1/L)=1 := by field_simp
    nlinarith
  have hp := hterm beta hb hbgap
  have hq := hterm gamma hg hggap
  rw [show 1+1/L-1=1/L by ring, one_div_one_div] at h
  linarith

theorem real_indices_unique {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    (p r : SymmetricCompletedZeroIndex chi)
    (hp : (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0)
    (hr : (Complex.Hadamard.divisorZeroIndex₀_val r).im = 0)
    (hpgap : 1-(Complex.Hadamard.divisorZeroIndex₀_val p).re < 1/(3*Real.log q))
    (hrgap : 1-(Complex.Hadamard.divisorZeroIndex₀_val r).re < 1/(3*Real.log q)) :
    p = r := by
  by_contra hne
  have hq := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hpstrip := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim p
  have hrstrip := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim r
  apply real_pair_contradiction (log_level_gt_one hq) hpstrip.2 hrstrip.2 hpgap hrgap
  intro sigma hs hs2
  have hh := two_real_kernel_le hchi hprim p r hne hs hs2
  have hpk := zeroKernel_re_of_same_im (s := (sigma : ℂ))
    (rho := Complex.Hadamard.divisorZeroIndex₀_val p)
    (by simpa using (ne_of_gt (hpstrip.2.trans hs)))
    (by simp [hp])
  have hrk := zeroKernel_re_of_same_im (s := (sigma : ℂ))
    (rho := Complex.Hadamard.divisorZeroIndex₀_val r)
    (by simpa using (ne_of_gt (hrstrip.2.trans hs)))
    (by simp [hr])
  simpa only [hpk, hrk, Complex.ofReal_re, one_div] using hh

theorem primitive_real_zeros_unique {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (hzs : chi.LFunction s = 0) (hzt : chi.LFunction t = 0)
    (hrs : s.im = 0) (hrt : t.im = 0)
    (hgs : 1-s.re < 1/(3*Real.log q)) (hgt : 1-t.re < 1/(3*Real.log q)) :
    s = t := by
  obtain ⟨p, hp⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hchi hprim hs hzs
  obtain ⟨r, hr⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hchi hprim ht hzt
  have he := real_indices_unique hchi hprim p r (by simpa only [hp] using hrs)
    (by simpa only [hr] using hrt) (by simpa only [hp] using hgs) (by simpa only [hr] using hgt)
  exact hp.symm.trans ((congrArg Complex.Hadamard.divisorZeroIndex₀_val he).trans hr)

theorem primitive_real_zero_simple {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {s : ℂ} (hs : 0 < s.re) (hz : chi.LFunction s = 0)
    (hr : s.im = 0) (hg : 1-s.re < 1/(3*Real.log q)) :
    analyticOrderNatAt chi.LFunction s = 1 := by
  classical
  obtain ⟨p, hp⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hchi hprim hs hz
  let fiber := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
    (f := symmetricCompletedLFunction chi) s
  have hfiber : fiber = {p} := by
    ext r
    rw [Finset.mem_singleton]
    constructor
    · intro hmem
      have hv := (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
        (f := symmetricCompletedLFunction chi) (z₀ := s) r).mp hmem
      exact real_indices_unique hchi hprim r p (by simpa only [hv] using hr)
        (by simpa only [hp] using hr) (by simpa only [hv] using hg) (by simpa only [hp] using hg)
    · intro he
      subst r
      exact (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
        (f := symmetricCompletedLFunction chi) (z₀ := s) p).mpr hp
  have hcard := Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (hf := differentiable_symmetricCompletedLFunction hchi) (z₀ := s)
    (by intro h; simp [h] at hs)
  change fiber.card = _ at hcard
  rw [hfiber, Finset.card_singleton] at hcard
  exact (analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction hchi hs).symm.trans hcard.symm

theorem real_zeros_unique {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (hzs : chi.LFunction s = 0) (hzt : chi.LFunction t = 0)
    (hrs : s.im = 0) (hrt : t.im = 0)
    (hgs : 1-s.re < 1/(3*Real.log chi.conductor))
    (hgt : 1-t.re < 1/(3*Real.log chi.conductor)) :
    s = t := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact primitive_real_zeros_unique
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive hs ht
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hchi hs hzs)
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hchi ht hzt)
    hrs hrt hgs hgt

theorem real_zero_simple {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (hz : chi.LFunction s = 0)
    (hr : s.im = 0) (hg : 1-s.re < 1/(3*Real.log chi.conductor)) :
    analyticOrderNatAt chi.LFunction s = 1 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rw [analyticOrderNatAt_LFunction_eq_primitive chi hchi hs]
  exact primitive_real_zero_simple
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi)
    chi.primitiveCharacter_isPrimitive hs
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hchi hs hz) hr hg

end LiuWang.Proof.ZeroRegionFamily
