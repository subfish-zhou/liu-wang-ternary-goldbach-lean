import LiuWang.Proof.LocalAnalyticBounds.HorizontalEstimate.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ZeroResidue
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.LogDerivativeSimple
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.MultiplicityBound
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # 实端点、中心 2.5 的整解析差商及实际留数 -/

set_option autoImplicit false
noncomputable section

open Filter Topology
open LiuWang.Proof.Interfaces
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.NonSymmetricContour

def centeredKernel (t : Real) : Complex → Complex :=
  dslope (fun s : Complex => (t : Complex) ^ s - (2.5 : Complex) ^ s) 0

theorem centeredKernel_eq {t : Real} {s : Complex} (hs : s ≠ 0) :
    centeredKernel t s = ((t : Complex) ^ s - (2.5 : Complex) ^ s) / s := by
  simp [centeredKernel, dslope_of_ne _ hs, slope, smul_eq_mul, div_eq_mul_inv,
    mul_comm]

theorem differentiable_centeredKernel {t : Real} (ht : 0 < t) :
    Differentiable Complex (centeredKernel t) := by
  have htC : (t : Complex) ≠ 0 := by exact_mod_cast ht.ne'
  have hd : Differentiable Complex
      (fun s : Complex => (t : Complex) ^ s - (2.5 : Complex) ^ s) :=
    (differentiable_id.const_cpow (Or.inl htC)).sub
      (differentiable_id.const_cpow (Or.inl (by norm_num)))
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (by simp : Set.univ ∈ 𝓝 (0 : Complex))).mpr
      hd.differentiableOn)

theorem centeredKernel_zero {t : Real} (ht : 0 < t) :
    centeredKernel t 0 = (Real.log (t / 2.5) : Complex) := by
  have htC : (t : Complex) ≠ 0 := by exact_mod_cast ht.ne'
  have hd := (Complex.hasStrictDerivAt_const_cpow
    (x := (t : Complex)) (y := (0 : Complex)) (Or.inl htC)).hasDerivAt.sub
      (Complex.hasStrictDerivAt_const_cpow
        (x := (2.5 : Complex)) (y := (0 : Complex)) (Or.inl (by norm_num))).hasDerivAt
  rw [centeredKernel, dslope_same]
  change deriv ((fun s : Complex => (t : Complex) ^ s) -
    fun s : Complex => (2.5 : Complex) ^ s) 0 = _
  rw [hd.deriv]
  simp only [Complex.cpow_zero, one_mul]
  rw [Real.log_div ht.ne' (by norm_num), Complex.ofReal_sub,
    Complex.ofReal_log ht.le, Complex.ofReal_log (by norm_num : (0 : Real) ≤ 2.5)]
  norm_num

def analyticIntegrand {q : Nat} [NeZero q] (chi : Character q) (t : Real) :
    Complex → Complex :=
  fun s => logDeriv chi.LFunction s * (-centeredKernel t s)

theorem analyticIntegrand_eq {q : Nat} [NeZero q] (chi : Character q)
    (t : Real) {s : Complex} (hs : s ≠ 0) :
    analyticIntegrand chi t s = LocalAnalyticBounds.HorizontalEstimate.horizontalIntegrand chi t s := by
  rw [analyticIntegrand, centeredKernel_eq hs]
  unfold LocalAnalyticBounds.HorizontalEstimate.horizontalIntegrand
  ring

theorem meromorphic_analyticIntegrand {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {t : Real} (ht : 0 < t) :
    Meromorphic (analyticIntegrand chi t) := by
  intro s
  exact (meromorphic_logDeriv_LFunction hchi s).mul
    ((differentiable_centeredKernel ht).analyticAt s).neg.meromorphicAt

theorem analyticAt_analyticIntegrand {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {t : Real} (ht : 0 < t) {s : Complex}
    (hs : chi.LFunction s ≠ 0) :
    AnalyticAt Complex (analyticIntegrand chi t) s := by
  have hL := (DirichletCharacter.differentiable_LFunction hchi).analyticAt s
  exact (hL.deriv.div hL hs).mul ((differentiable_centeredKernel ht).analyticAt s).neg

theorem simple_analyticIntegrand {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {t : Real} (ht : 0 < t) (U : Set Complex) :
    HasSimplePolesOn (analyticIntegrand chi t) U := by
  intro s hs
  have hk := ((differentiable_centeredKernel ht).analyticAt s).neg
  change (-1 : Int) ≤ meromorphicOrderAt
    (logDeriv chi.LFunction * (-centeredKernel t)) s
  rw [meromorphicOrderAt_mul (meromorphic_logDeriv_LFunction hchi s) hk.meromorphicAt]
  simpa using add_le_add (hasSimplePolesOn_logDeriv_LFunction hchi U s hs)
    hk.meromorphicOrderAt_nonneg

theorem residue_analyticIntegrand {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {t : Real} (ht : 0 < t) (rho : Complex) :
    residue (analyticIntegrand chi t) rho =
      -(analyticOrderNatAt chi.LFunction rho : Complex) * centeredKernel t rho := by
  have hA := (DirichletCharacter.differentiable_LFunction hchi).analyticAt rho
  have hfinite : analyticOrderAt chi.LFunction rho ≠ ⊤ := by
    intro h
    apply meromorphicOrderAt_LFunction_ne_top hchi rho
    simpa [h] using hA.meromorphicOrderAt_eq
  have hord : meromorphicOrderAt chi.LFunction rho =
      ((analyticOrderNatAt chi.LFunction rho : Int) : WithTop Int) := by
    rw [hA.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hfinite]
    simp
  have hp := logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hA.meromorphicAt hord
  have hr := Kadiri.residue_mul_eq_of_sub_principal_isBigO_one hp
    (differentiable_centeredKernel ht).continuous.continuousAt.neg
  change residue (fun z => logDeriv chi.LFunction z * (-centeredKernel t z)) rho = _
  simpa using hr

theorem residue_analyticIntegrand_zero {q : Nat} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) {t : Real} (ht : 0 < t) :
    residue (analyticIntegrand chi t) 0 =
      -(lFunctionOriginMultiplicity chi : Complex) * (Real.log (t / 2.5) : Complex) := by
  rw [residue_analyticIntegrand hchi ht, centeredKernel_zero ht]
  rfl

end LiuWang.Proof.NonSymmetricContour
