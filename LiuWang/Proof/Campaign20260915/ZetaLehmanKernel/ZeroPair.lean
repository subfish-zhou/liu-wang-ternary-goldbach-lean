import LiuWang.Proof.Campaign20260915.ZetaLehmanKernel.PairedKernel
import LiuWang.Proof.ZeroRegionFamily.Sharp.ZetaKernel

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate

namespace LiuWang.Proof.Campaign20260915.ZetaLehmanKernel

open LiuWang.Proof.Campaign20260915.ZetaWinding
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.PrincipalPsi.Quantitative
open LiuWang.Proof.ChebyshevBound.HighHeight
open BombieriVinogradov.SiegelWalfisz

def zeroIntegral (rho : ℂ) (T : ℝ) : ℝ :=
  ∫ x in (1 / 2 : ℝ)..(3 / 2),
    Real.log ‖(horizontalAt T x - rho) / (horizontalAt T (x + 1) - rho)‖

def referenceTerm (rho : ℂ) (T : ℝ) : ℝ :=
  (1 / (horizontalAt T (3 / 2) - rho)).re

theorem zeroIntegral_eq_neg_loss (rho : ℂ) (T : ℝ) :
    zeroIntegral rho T = -zeroLoss (1 / 2 - rho.re) (T - rho.im) := by
  unfold zeroIntegral
  rw [integral_log_norm_zero_ratio]
  unfold zeroLoss
  rw [show 1 / 2 - rho.re + 2 = 3 / 2 + 1 - rho.re by ring,
    show 1 / 2 - rho.re + 1 = 3 / 2 - rho.re by ring,
    show 1 / 2 + 1 - rho.re = 3 / 2 - rho.re by ring]
  ring

theorem referenceTerm_eq (rho : ℂ) (T : ℝ) :
    referenceTerm rho T =
      (3 / 2 - rho.re) / ((3 / 2 - rho.re) ^ 2 + (T - rho.im) ^ 2) := by
  simp [referenceTerm, horizontalAt, one_div, inv_re, normSq_apply]
  ring

theorem zeroIntegral_pair_lehman {rho : ℂ} (hr : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ) :
    -(37 / 25 : ℝ) * (referenceTerm rho T + referenceTerm (1 - conj rho) T) ≤
      zeroIntegral rho T + zeroIntegral (1 - conj rho) T := by
  have ha : |1 / 2 - rho.re| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h := zeroLoss_pair_lehman ha (T - rho.im)
  have he : referencePair (1 / 2 - rho.re) (T - rho.im) =
      referenceTerm rho T + referenceTerm (1 - conj rho) T := by
    rw [referenceTerm_eq, referenceTerm_eq]
    simp only [referencePair, sub_re, one_re, conj_re, sub_im, one_im, conj_im]
    ring_nf
  rw [he] at h
  rw [zeroIntegral_eq_neg_loss, zeroIntegral_eq_neg_loss]
  have hre : 1 / 2 - (1 - conj rho).re = -(1 / 2 - rho.re) := by simp; ring
  have him : T - (1 - conj rho).im = T - rho.im := by simp
  rw [hre, him]
  linarith

theorem xi_reference_ne_zero (T : ℝ) :
    ∀ p : RiemannXiDivisorZeroIndex,
      horizontalAt T (3 / 2) ≠ riemannXiDivisorZeroValue p := by
  intro p he
  have h := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  rw [← he] at h
  norm_num [horizontalAt] at h

theorem xi_zero_pair_lehman (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    -(37 / 25 : ℝ) *
        (referenceTerm (riemannXiDivisorZeroValue p) T +
          referenceTerm (riemannXiDivisorZeroValue (xiReflection p)) T) ≤
      zeroIntegral (riemannXiDivisorZeroValue p) T +
        zeroIntegral (riemannXiDivisorZeroValue (xiReflection p)) T := by
  rw [show riemannXiDivisorZeroValue (xiReflection p) =
    1 - conj (riemannXiDivisorZeroValue p) from rfl]
  exact zeroIntegral_pair_lehman
    ⟨(riemannXiDivisorZeroValue_re_mem_Ioo p).1.le,
      (riemannXiDivisorZeroValue_re_mem_Ioo p).2.le⟩ T

#print axioms zeroIntegral_pair_lehman
#print axioms xi_zero_pair_lehman
#print axioms xiReflection

end LiuWang.Proof.Campaign20260915.ZetaLehmanKernel
