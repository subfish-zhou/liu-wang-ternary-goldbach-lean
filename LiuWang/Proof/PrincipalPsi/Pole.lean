import LiuWang.Proof.NonSymmetricContour.Kernel
import LiuWang.Proof.ChebyshevBound.ZetaLocal

/-!
# 主字符的实际极点与居中 Perron 核

`LFunctionTrivChar₁` 是在 1 补上非零极限的整函数，不是普通 L 函数
在 1 的总定义点值。以下亚纯阶与留数均由穿孔邻域上的恒等式得到。
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.PrincipalPsi

abbrev regularizedPrincipal (q : ℕ) [NeZero q] : ℂ → ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ q

theorem regularizedPrincipal_eq {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    regularizedPrincipal q s = (s - 1) * (1 : DirichletCharacter ℂ q).LFunction s :=
  Function.update_of_ne hs _ _

theorem analytic_regularizedPrincipal (q : ℕ) [NeZero q] (s : ℂ) :
    AnalyticAt ℂ (regularizedPrincipal q) s :=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt s

theorem regularizedPrincipal_one_ne_zero (q : ℕ) [NeZero q] :
    regularizedPrincipal q 1 ≠ 0 :=
  DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q

theorem principal_eq_regularized_div {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction s = regularizedPrincipal q s / (s - 1) := by
  rw [regularizedPrincipal_eq hs]
  field_simp

theorem principal_eq_regularized_div_nhdsNE (q : ℕ) [NeZero q] :
    (1 : DirichletCharacter ℂ q).LFunction =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s => regularizedPrincipal q s / (s - 1) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact principal_eq_regularized_div hs

theorem meromorphic_principal (q : ℕ) [NeZero q] :
    Meromorphic (1 : DirichletCharacter ℂ q).LFunction := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact ((analytic_regularizedPrincipal q 1).meromorphicAt.div
      (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 1)).congr
        (principal_eq_regularized_div_nhdsNE q).symm
  · have hA : AnalyticOnNhd ℂ (1 : DirichletCharacter ℂ q).LFunction {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (DirichletCharacter.differentiableAt_LFunction 1 z
          (.inl hz)).differentiableWithinAt) isOpen_compl_singleton
    exact (hA s hs).meromorphicAt

theorem meromorphicOrderAt_principal_one (q : ℕ) [NeZero q] :
    meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction 1 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_congr (principal_eq_regularized_div_nhdsNE q)]
  change meromorphicOrderAt ((regularizedPrincipal q) / fun z : ℂ => z - 1) 1 = _
  rw [meromorphicOrderAt_div (analytic_regularizedPrincipal q 1).meromorphicAt
      (by fun_prop), (analytic_regularizedPrincipal q 1).meromorphicOrderAt_eq,
    (analytic_regularizedPrincipal q 1).analyticOrderAt_eq_zero.mpr
      (regularizedPrincipal_one_ne_zero q), meromorphicOrderAt_id_sub_const]
  norm_num

theorem meromorphicOrderAt_principal_ne_top (q : ℕ) [NeZero q] (s : ℂ) :
    meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction s ≠ ⊤ := by
  apply ((meromorphic_principal q).exists_meromorphicOrderAt_ne_top_iff_forall).mp
  exact ⟨1, by rw [meromorphicOrderAt_principal_one]; simp⟩

theorem meromorphic_principal_logDeriv (q : ℕ) [NeZero q] :
    Meromorphic (logDeriv (1 : DirichletCharacter ℂ q).LFunction) :=
  (meromorphic_principal q).logDeriv

theorem simple_principal_logDeriv (q : ℕ) [NeZero q] (U : Set ℂ) :
    HasSimplePolesOn (logDeriv (1 : DirichletCharacter ℂ q).LFunction) U :=
  logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top
    (meromorphic_principal q).meromorphicOn
    (meromorphic_principal_logDeriv q).meromorphicOn
    (fun s _ => meromorphicOrderAt_principal_ne_top q s)

theorem principal_centered_residue_one (q : ℕ) [NeZero q]
    {t : ℝ} (ht : 0 < t) :
    residue (NonSymmetricContour.analyticIntegrand (1 : DirichletCharacter ℂ q) t) 1 =
      (t : ℂ) - 2.5 := by
  have hprincipal := logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
    (meromorphic_principal q 1) (meromorphicOrderAt_principal_one q)
  have hres := Kadiri.residue_mul_eq_of_sub_principal_isBigO_one hprincipal
    (NonSymmetricContour.differentiable_centeredKernel ht).continuous.continuousAt.neg
  change residue (fun s => logDeriv (1 : DirichletCharacter ℂ q).LFunction s *
    (-NonSymmetricContour.centeredKernel t s)) 1 = _
  simpa [NonSymmetricContour.centeredKernel_eq (by norm_num : (1 : ℂ) ≠ 0)] using hres

theorem zeta_centered_residue_one {t : ℝ} (ht : 0 < t) :
    residue (fun s => -logDeriv riemannZeta s *
      NonSymmetricContour.centeredKernel t s) 1 = (t : ℂ) - 2.5 := by
  have h := principal_centered_residue_one 1 ht
  change residue (fun s => logDeriv (1 : DirichletCharacter ℂ 1).LFunction s *
    (-NonSymmetricContour.centeredKernel t s)) 1 = _ at h
  simpa only [DirichletCharacter.LFunction_modOne_eq, neg_mul, mul_neg] using h

theorem zeta_centered_kernel_at_pole (t : ℝ) :
    NonSymmetricContour.centeredKernel t 1 = (t : ℂ) - 2.5 := by
  simp [NonSymmetricContour.centeredKernel_eq (by norm_num : (1 : ℂ) ≠ 0)]

end LiuWang.Proof.PrincipalPsi
