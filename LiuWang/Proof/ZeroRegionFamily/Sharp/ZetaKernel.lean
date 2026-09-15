import LiuWang.Proof.ZeroRegionFamily.Sharp.Euler
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorConjugation
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # ζ的真实去极点恒等式与保重数Stechkin差核 -/

set_option autoImplicit false
noncomputable section

open Complex Filter
open scoped Topology ComplexConjugate
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem xi_product {s : ℂ} (hs : 1 < s.re) :
    riemannXi s = s*(s-1)/2*
      ((1 : DirichletCharacter ℂ 1).gammaFactor s*riemannZeta s) := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta hs0
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))]
  have he : (1 : DirichletCharacter ℂ 1).Even :=
    MulChar.one_apply (isUnit_one.neg)
  rw [he.gammaFactor_def, Complex.Gammaℝ_def]
  ring

theorem xi_conj (s : ℂ) : riemannXi s = conj (riemannXi (conj s)) := by
  let g : ℂ → ℂ := conj ∘ riemannXi ∘ conj
  have hg : Differentiable ℂ g := by
    intro z
    have hh := (differentiable_riemannXi.differentiableAt
      (x := conj z)).conj_conj
    simpa only [Complex.conj_conj] using hh
  have he : riemannXi =ᶠ[𝓝 (2 : ℂ)] g := by
    have hright : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hright] with z hz
    dsimp [g]
    rw [xi_product hz, xi_product (by simpa using hz)]
    have hgamma := DirichletCharacter.gammaFactor_inv_eq_conj_conj
      (1 : DirichletCharacter ℂ 1) z
    simp only [inv_one] at hgamma
    rw [map_mul, map_div₀, map_mul, map_sub, map_one, Complex.conj_conj, map_ofNat,
      map_mul, ← hgamma, riemannZeta_conj, Complex.conj_conj]
  have hh := AnalyticOnNhd.eq_of_eventuallyEq
    (differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ) he
  exact congrFun hh s

theorem xi_reflected_order (rho : ℂ) :
    analyticOrderNatAt riemannXi (1-conj rho)=analyticOrderNatAt riemannXi rho := by
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := riemannXi) (g := fun s : ℂ => 1-s) (z₀ := conj rho)
    (by fun_prop) (by simp)
  have he : (fun s : ℂ => riemannXi (1-s))=riemannXi := funext riemannXi_one_sub
  change analyticOrderAt (fun s : ℂ => riemannXi (1-s)) (conj rho)=_ at hcomp
  rw [he] at hcomp
  have hconj := BombieriVinogradov.ComplexAnalysis.AnalyticAt.analyticOrderNatAt_conj_conj
    (f := riemannXi) (z := conj rho) (differentiable_riemannXi.analyticAt _)
  have heg : (fun s : ℂ => conj (riemannXi (conj s)))=riemannXi := (funext xi_conj).symm
  rw [heg, Complex.conj_conj] at hconj
  have hh := congrArg ENat.toNat hcomp
  change analyticOrderNatAt riemannXi (conj rho)=analyticOrderNatAt riemannXi (1-conj rho) at hh
  exact hh.symm.trans hconj

theorem xi_reflected_multiplicity (rho : ℂ) :
    (MeromorphicOn.divisor riemannXi Set.univ (1-conj rho)).toNat =
      (MeromorphicOn.divisor riemannXi Set.univ rho).toNat := by
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi,
    Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi]
  simpa using xi_reflected_order rho

def xiReflect (p : RiemannXiDivisorZeroIndex) : RiemannXiDivisorZeroIndex :=
  ⟨⟨1-conj (riemannXiDivisorZeroValue p),
      Fin.cast (xi_reflected_multiplicity (riemannXiDivisorZeroValue p)).symm p.val.2⟩, by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hr
    linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]⟩

theorem xiReflect_val (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (xiReflect p)=1-conj (riemannXiDivisorZeroValue p) := rfl

theorem xiReflect_involutive : Function.Involutive xiReflect := by
  intro p
  have hv : riemannXiDivisorZeroValue (xiReflect (xiReflect p))=riemannXiDivisorZeroValue p := by
    rw [xiReflect_val, xiReflect_val]
    simp
  have hc := congrArg (fun z : ℂ => (MeromorphicOn.divisor riemannXi Set.univ z).toNat) hv
  apply Subtype.ext
  apply Sigma.ext hv
  exact (Fin.heq_ext_iff hc).2 rfl

def xiReflection : RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  Equiv.ofBijective xiReflect ⟨xiReflect_involutive.injective, xiReflect_involutive.surjective⟩

def xiDampedTerm (sigma t : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  (xiTerm ((sigma : ℂ)+Complex.I*t) p).re-
    stechkinK*(xiTerm ((stechkinSigma sigma : ℂ)+Complex.I*t) p).re

theorem xiDampedTerm_summable {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    Summable (xiDampedTerm sigma t) := by
  exact (Complex.reCLM.summable (xiTerm_summable
    (by simpa [Complex.mul_re] using hs.le))).sub
      ((Complex.reCLM.summable (xiTerm_summable
        (by simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le))).mul_left stechkinK)

theorem xiDamped_sum_nonneg {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    0 ≤ ∑' p, xiDampedTerm sigma t p := by
  have hsum := xiDampedTerm_summable hs t
  have hcomp : Summable (fun p => xiDampedTerm sigma t (xiReflection p)) :=
    xiReflection.summable_iff.mpr hsum
  have hnon : 0 ≤ ∑' p, (xiDampedTerm sigma t p+xiDampedTerm sigma t (xiReflection p)) := by
    apply tsum_nonneg
    intro p
    have hp := riemannXiDivisorZeroValue_re_mem_Ioo p
    have hpair := dampedZeroKernel_pair_nonneg hs t ⟨hp.1.le, hp.2.le⟩
    have hpos (q : RiemannXiDivisorZeroIndex) : 0 ≤ (1/riemannXiDivisorZeroValue q).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg (riemannXiDivisorZeroValue_re_mem_Ioo q).1.le (Complex.normSq_nonneg _)
    have h0 := mul_nonneg (sub_nonneg.mpr stechkinK_mem.2) (hpos p)
    have h1 := mul_nonneg (sub_nonneg.mpr stechkinK_mem.2) (hpos (xiReflection p))
    have hval : riemannXiDivisorZeroValue (xiReflection p)=1-conj (riemannXiDivisorZeroValue p) := rfl
    simp only [xiDampedTerm, xiTerm, Complex.add_re, dampedZeroKernel] at *
    rw [hval] at h1 ⊢
    nlinarith
  rw [hsum.tsum_add hcomp, xiReflection.tsum_eq] at hnon
  linarith

def zetaDamped (sigma t : ℝ) : ℝ :=
  -(logDeriv riemannZeta ((sigma : ℂ)+Complex.I*t)).re+
    stechkinK*(logDeriv riemannZeta ((stechkinSigma sigma : ℂ)+Complex.I*t)).re

def poleDifference (sigma t : ℝ) : ℝ :=
  (1/((sigma : ℂ)-1+Complex.I*t)).re-
    stechkinK*(1/((stechkinSigma sigma : ℂ)-1+Complex.I*t)).re

def shiftedGammaDifference (sigma t : ℝ) : ℝ :=
  -stechkinConductorCoeff*Real.log Real.pi+
    ((Complex.digamma (((sigma : ℂ)+Complex.I*t)/2+1)).re-
      stechkinK*(Complex.digamma (((stechkinSigma sigma : ℂ)+Complex.I*t)/2+1)).re)/2

theorem zeta_damped_identity {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    zetaDamped sigma t+(∑' p, xiDampedTerm sigma t p) =
      -(1-stechkinK)*(logDeriv riemannXi 0).re+
        poleDifference sigma t+shiftedGammaDifference sigma t := by
  have h0 : 1 < ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs
  have h1 : 1 < ((stechkinSigma sigma : ℂ)+Complex.I*t).re := by
    simpa [Complex.mul_re] using hs.trans_le (stechkinSigma_ge hs)
  have hz0 := congrArg Complex.re (Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum h0)
  have hz1 := congrArg Complex.re (Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum h1)
  have hsum0 := Complex.reCLM.summable (xiTerm_summable h0.le)
  have hsum1 := Complex.reCLM.summable (xiTerm_summable h1.le)
  change Summable (fun p => (xiTerm ((sigma : ℂ)+Complex.I*t) p).re) at hsum0
  change Summable (fun p => (xiTerm ((stechkinSigma sigma : ℂ)+Complex.I*t) p).re) at hsum1
  have he : (∑' p, xiDampedTerm sigma t p) =
      (∑' p, xiTerm ((sigma : ℂ)+Complex.I*t) p).re-
      stechkinK*(∑' p, xiTerm ((stechkinSigma sigma : ℂ)+Complex.I*t) p).re := by
    rw [Complex.re_tsum (xiTerm_summable h0.le), Complex.re_tsum (xiTerm_summable h1.le)]
    exact hsum0.tsum_sub (hsum1.mul_left stechkinK) |>.trans (by rw [tsum_mul_left])
  rw [he]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, zero_div, zero_mul, sub_zero,
    neg_div, ← logDeriv_apply] at hz0 hz1
  have hp (u : ℝ) : (u : ℂ)+Complex.I*t-1=(u : ℂ)-1+Complex.I*t := by ring
  rw [hp] at hz0 hz1
  dsimp [zetaDamped, poleDifference, shiftedGammaDifference, stechkinConductorCoeff, xiTerm] at *
  linear_combination hz0-stechkinK*hz1

theorem zeta_damped_le {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    zetaDamped sigma t ≤ -(1-stechkinK)*(logDeriv riemannXi 0).re+
      poleDifference sigma t+shiftedGammaDifference sigma t := by
  linarith [zeta_damped_identity hs t, xiDamped_sum_nonneg hs t]

theorem xi_inv_re_summable :
    Summable (fun p : RiemannXiDivisorZeroIndex => (1/riemannXiDivisorZeroValue p).re) := by
  apply Summable.of_nonneg_of_le
    (f := fun p : RiemannXiDivisorZeroIndex => ‖riemannXiDivisorZeroValue p‖⁻¹^2)
    _ _ summable_riemannXiDivisorZero_norm_inv_sq
  · intro p
    rw [one_div, Complex.inv_re]
    exact div_nonneg (riemannXiDivisorZeroValue_re_mem_Ioo p).1.le (Complex.normSq_nonneg _)
  · intro p
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    have hh := div_le_div_of_nonneg_right (riemannXiDivisorZeroValue_re_mem_Ioo p).2.le
      (sq_nonneg ‖riemannXiDivisorZeroValue p‖)
    simpa [one_div, inv_pow] using hh

theorem xi_inv_re_sum :
    (∑' p : RiemannXiDivisorZeroIndex, (1/riemannXiDivisorZeroValue p).re) =
      -(logDeriv riemannXi 0).re := by
  have href : (fun p : RiemannXiDivisorZeroIndex => (1/(1-riemannXiDivisorZeroValue p)).re) =
      (fun p => (1/riemannXiDivisorZeroValue (xiReflection p)).re) := by
    funext p
    change _ = (1/(1-conj (riemannXiDivisorZeroValue p))).re
    simpa only [map_sub, map_one, Complex.conj_re] using
      congrArg Complex.re (map_div₀ (starRingEnd ℂ) (1 : ℂ) (1-riemannXiDivisorZeroValue p))
  have hsref : Summable (fun p : RiemannXiDivisorZeroIndex => (1/(1-riemannXiDivisorZeroValue p)).re) := by
    rw [href]
    exact xiReflection.summable_iff.mpr xi_inv_re_summable
  have h := congrArg Complex.re xiTerm_sum_one
  rw [Complex.re_tsum (xiTerm_summable (s := 1) (by norm_num))] at h
  simp only [xiTerm, Complex.add_re] at h
  rw [hsref.tsum_add xi_inv_re_summable, href,
    xiReflection.tsum_eq (fun p => (1/riemannXiDivisorZeroValue p).re)] at h
  have hc := congrArg Complex.re neg_two_mul_logDeriv_riemannXi_zero_eq
  norm_num [Complex.mul_re] at hc h
  simp only [one_div, Complex.inv_re]
  linarith

theorem xi_raw_summable {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (fun p : RiemannXiDivisorZeroIndex => (1/(s-riemannXiDivisorZeroValue p)).re) := by
  have hh := (Complex.reCLM.summable (xiTerm_summable hs)).sub xi_inv_re_summable
  simpa [xiTerm] using hh

theorem xi_raw_damped_nonneg {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    0 ≤ ∑' p : RiemannXiDivisorZeroIndex, dampedZeroKernel sigma t (riemannXiDivisorZeroValue p) := by
  let f := fun p : RiemannXiDivisorZeroIndex => dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)
  have h0 : 1 ≤ ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs.le
  have h1 : 1 ≤ ((stechkinSigma sigma : ℂ)+Complex.I*t).re := by
    simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le
  have hf : Summable f := (xi_raw_summable h0).sub ((xi_raw_summable h1).mul_left stechkinK)
  have he : Summable (fun p => f (xiReflection p)) := xiReflection.summable_iff.mpr hf
  have hn : 0 ≤ ∑' p, (f p+f (xiReflection p)) := by
    apply tsum_nonneg
    intro p
    exact dampedZeroKernel_pair_nonneg hs t
      ⟨(riemannXiDivisorZeroValue_re_mem_Ioo p).1.le, (riemannXiDivisorZeroValue_re_mem_Ioo p).2.le⟩
  rw [hf.tsum_add he, xiReflection.tsum_eq] at hn
  change 0 ≤ ∑' p, f p
  linarith

theorem zeta_damped_pole_bound {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    zetaDamped sigma t ≤ poleDifference sigma t+shiftedGammaDifference sigma t := by
  have hi := zeta_damped_identity hs t
  have hn := xi_raw_damped_nonneg hs t
  have h0 : 1 ≤ ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs.le
  have h1 : 1 ≤ ((stechkinSigma sigma : ℂ)+Complex.I*t).re := by
    simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le
  have hf := (xi_raw_summable h0).sub ((xi_raw_summable h1).mul_left stechkinK)
  change Summable (fun p : RiemannXiDivisorZeroIndex =>
    dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)) at hf
  have he : (∑' p, xiDampedTerm sigma t p) =
      (∑' p, dampedZeroKernel sigma t (riemannXiDivisorZeroValue p))-
      (1-stechkinK)*(logDeriv riemannXi 0).re := by
    have hid : xiDampedTerm sigma t =
        fun p => dampedZeroKernel sigma t (riemannXiDivisorZeroValue p)+
          (1-stechkinK)*(1/riemannXiDivisorZeroValue p).re := by
      funext p
      simp only [xiDampedTerm, xiTerm, Complex.add_re, dampedZeroKernel]
      ring
    simp only [hid]
    rw [hf.tsum_add (xi_inv_re_summable.mul_left (1-stechkinK)),
      tsum_mul_left, xi_inv_re_sum]
    ring
  rw [he] at hi
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
