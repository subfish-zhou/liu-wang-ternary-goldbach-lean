import LiuWang.Proof.PrincipalPsi.EulerTransport

/-!
# 实际 ζ 居中被积函数的解析结构

此处证明全平面亚纯性、简单极点和实际零点留数，不假设 ζ 没有低零点。
定量轮廓的避零高度与边界估计不包含在这些局部留数结论中。
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.PrincipalPsi

def zetaCenteredIntegrand (t : ℝ) (s : ℂ) : ℂ :=
  logDeriv riemannZeta s * (-NonSymmetricContour.centeredKernel t s)

theorem zetaCenteredIntegrand_eq {t : ℝ} {s : ℂ} (hs : s ≠ 0) :
    zetaCenteredIntegrand t s =
      -logDeriv riemannZeta s * (((t : ℂ) ^ s - (2.5 : ℂ) ^ s) / s) := by
  rw [zetaCenteredIntegrand, NonSymmetricContour.centeredKernel_eq hs]
  ring

theorem meromorphic_zetaCenteredIntegrand {t : ℝ} (ht : 0 < t) :
    Meromorphic (zetaCenteredIntegrand t) := by
  have hm : Meromorphic (logDeriv riemannZeta) := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_principal_logDeriv 1
  intro s
  exact (hm s).mul
    (((NonSymmetricContour.differentiable_centeredKernel ht).analyticAt s).neg.meromorphicAt)

theorem simple_zetaCenteredIntegrand {t : ℝ} (ht : 0 < t) (U : Set ℂ) :
    HasSimplePolesOn (zetaCenteredIntegrand t) U := by
  have hm : Meromorphic (logDeriv riemannZeta) := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_principal_logDeriv 1
  have hp : HasSimplePolesOn (logDeriv riemannZeta) U := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using simple_principal_logDeriv 1 U
  intro s hs
  have hk := ((NonSymmetricContour.differentiable_centeredKernel ht).analyticAt s).neg
  change (-1 : ℤ) ≤ meromorphicOrderAt
    (logDeriv riemannZeta * (-NonSymmetricContour.centeredKernel t)) s
  rw [meromorphicOrderAt_mul (hm s) hk.meromorphicAt]
  simpa using add_le_add (hp s hs) hk.meromorphicOrderAt_nonneg

theorem analytic_zetaCenteredIntegrand {t : ℝ} (ht : 0 < t) {s : ℂ}
    (hs1 : s ≠ 1) (hs : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (zetaCenteredIntegrand t) s := by
  have hA := analytic_zeta_of_ne_one hs1
  exact (hA.deriv.div hA hs).mul
    ((NonSymmetricContour.differentiable_centeredKernel ht).analyticAt s).neg

theorem residue_zetaCenteredIntegrand_one {t : ℝ} (ht : 0 < t) :
    residue (zetaCenteredIntegrand t) 1 = (t : ℂ) - 2.5 := by
  unfold zetaCenteredIntegrand
  simpa only [mul_neg, neg_mul] using zeta_centered_residue_one ht

theorem residue_zetaCenteredIntegrand_of_ne_one {t : ℝ} (ht : 0 < t) {rho : ℂ}
    (hrho : rho ≠ 1) :
    residue (zetaCenteredIntegrand t) rho =
      -(analyticOrderNatAt riemannZeta rho : ℂ) * NonSymmetricContour.centeredKernel t rho := by
  have hA := analytic_zeta_of_ne_one hrho
  have hm : meromorphicOrderAt riemannZeta rho ≠ ⊤ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphicOrderAt_principal_ne_top 1 rho
  have hfinite : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    intro h
    apply hm
    simp [hA.meromorphicOrderAt_eq, h]
  have hord : meromorphicOrderAt riemannZeta rho =
      ((analyticOrderNatAt riemannZeta rho : ℤ) : WithTop ℤ) := by
    rw [hA.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hfinite]
    simp
  have hprincipal := logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hA.meromorphicAt hord
  have hres := Kadiri.residue_mul_eq_of_sub_principal_isBigO_one hprincipal
    (NonSymmetricContour.differentiable_centeredKernel ht).continuous.continuousAt.neg
  unfold zetaCenteredIntegrand
  simpa using hres

theorem residue_zetaCenteredIntegrand_zero {t : ℝ} (ht : 0 < t) :
    residue (zetaCenteredIntegrand t) 0 = 0 := by
  rw [residue_zetaCenteredIntegrand_of_ne_one ht (by norm_num)]
  have horder : analyticOrderNatAt riemannZeta 0 = 0 := by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr
      (.inr (by simp [riemannZeta_zero] : riemannZeta 0 ≠ 0))]
  simp [horder]

theorem zetaCenteredIntegrand_poles_subset {t : ℝ} (ht : 0 < t) {s : ℂ}
    (hs : meromorphicOrderAt (zetaCenteredIntegrand t) s < 0) :
    s = 1 ∨ riemannZeta s = 0 := by
  by_cases hs1 : s = 1
  · exact Or.inl hs1
  · right
    by_contra hn
    exact not_lt_of_ge (analytic_zetaCenteredIntegrand ht hs1 hn).meromorphicOrderAt_nonneg hs

end LiuWang.Proof.PrincipalPsi
