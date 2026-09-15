import LiuWang.Proof.PrincipalPsi.Pole
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionFactorNonvanishing

/-!
# 主字符有限 Euler 因子的真实非零性与重数运输

仅在 `Re s > 0` 且 `s ≠ 1` 运输普通 L 函数的零点及解析重数。
极点另由 `Pole` 处理，不以总定义点值代替解析信息。
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped BigOperators

namespace LiuWang.Proof.PrincipalPsi

def principalEuler (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

theorem differentiable_principalEuler (q : ℕ) :
    Differentiable ℂ (principalEuler q) := by
  intro s
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  fun_prop

theorem principalEuler_ne_zero {q : ℕ} {s : ℂ} (hs : 0 < s.re) :
    principalEuler q s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hnorm := BombieriVinogradov.SiegelWalfisz.norm_prime_cpow_lt_one_of_re_pos
    (Nat.prime_of_mem_primeFactors hp) hs
  intro h
  have heq : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  simp [heq] at hnorm

theorem principal_eq_euler_mul_zeta {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction s = principalEuler q s * riemannZeta s :=
  DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs

theorem principal_eq_euler_mul_zeta_nhds {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction =ᶠ[𝓝 s]
      fun z => principalEuler q z * riemannZeta z := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
  exact principal_eq_euler_mul_zeta hz

theorem analytic_principal_of_ne_one {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (1 : DirichletCharacter ℂ q).LFunction s := by
  exact DifferentiableOn.analyticOnNhd
    (fun z hz => (DirichletCharacter.differentiableAt_LFunction 1 z
      (.inl hz)).differentiableWithinAt) isOpen_compl_singleton s hs

theorem analytic_zeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    (analytic_principal_of_ne_one (q := 1) hs)

theorem principal_zero_iff_zeta_zero {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction s = 0 ↔ riemannZeta s = 0 := by
  rw [principal_eq_euler_mul_zeta hs1, mul_eq_zero]
  simp only [principalEuler_ne_zero hs, false_or]

theorem analyticOrderAt_principal_eq_zeta {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt (1 : DirichletCharacter ℂ q).LFunction s =
      analyticOrderAt riemannZeta s := by
  rw [analyticOrderAt_congr (principal_eq_euler_mul_zeta_nhds hs1)]
  change analyticOrderAt (principalEuler q * riemannZeta) s = _
  rw [analyticOrderAt_mul ((differentiable_principalEuler q).analyticAt s)
      (analytic_zeta_of_ne_one hs1),
    ((differentiable_principalEuler q).analyticAt s).analyticOrderAt_eq_zero.mpr
      (principalEuler_ne_zero hs), zero_add]

theorem analyticOrderNatAt_principal_eq_zeta {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction s =
      analyticOrderNatAt riemannZeta s := by
  simp only [analyticOrderNatAt, analyticOrderAt_principal_eq_zeta hs hs1]

theorem analyticOrderAt_regularized_eq_principal {q : ℕ} [NeZero q] {s : ℂ}
    (hs : s ≠ 1) :
    analyticOrderAt (regularizedPrincipal q) s =
      analyticOrderAt (1 : DirichletCharacter ℂ q).LFunction s := by
  have heq : regularizedPrincipal q =ᶠ[𝓝 s]
      fun z => (z - 1) * (1 : DirichletCharacter ℂ q).LFunction z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact regularizedPrincipal_eq hz
  rw [analyticOrderAt_congr heq]
  change analyticOrderAt ((fun z : ℂ => z - 1) *
    (1 : DirichletCharacter ℂ q).LFunction) s = _
  rw [analyticOrderAt_mul (by fun_prop) (analytic_principal_of_ne_one hs),
    analyticOrderAt_eq_zero (f := fun z : ℂ => z - 1) |>.mpr
      (.inr (sub_ne_zero.mpr hs)), zero_add]

theorem analyticOrderNatAt_regularized_eq_principal {q : ℕ} [NeZero q] {s : ℂ}
    (hs : s ≠ 1) :
    analyticOrderNatAt (regularizedPrincipal q) s =
      analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction s := by
  simp only [analyticOrderNatAt, analyticOrderAt_regularized_eq_principal hs]

end LiuWang.Proof.PrincipalPsi
