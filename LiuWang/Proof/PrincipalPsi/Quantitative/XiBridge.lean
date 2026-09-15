import LiuWang.Proof.PrincipalPsi.ClosedZeros
import LiuWang.Proof.ChebyshevBound.HighHeight.ZeroTail

/-! # 实际 xi 与主字符去极点函数：非零解析因子和重数桥 -/

set_option autoImplicit false
noncomputable section

open Complex Filter Topology
open scoped BigOperators

namespace LiuWang.Proof.PrincipalPsi.Quantitative

def xiFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1)

theorem analytic_xiFactor {s : ℂ} (hs : -2 < s.re) :
    AnalyticAt ℂ xiFactor s := by
  have hdiff : DifferentiableOn ℂ xiFactor {z : ℂ | -2 < z.re} := by
    intro z hz
    have hg : ∀ n : ℕ, z / 2 + 1 ≠ -(n : ℂ) := by
      intro n hn
      have h := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.neg_re, Complex.natCast_re] at h
      have hnn := Nat.cast_nonneg (α := ℝ) n
      change -2 < z.re at hz
      linarith
    exact ((differentiableAt_id.neg.div_const 2).const_cpow
      (.inl (by exact_mod_cast Real.pi_ne_zero))).mul
      ((differentiableAt_Gamma _ hg).comp z
        ((differentiableAt_id.div_const 2).add_const 1)) |>.differentiableWithinAt
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) s hs

theorem xiFactor_ne_zero {s : ℂ} (hs : -2 < s.re) : xiFactor s ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast Real.pi_ne_zero))
  · exact Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
      linarith)

theorem xi_eq_factor_regularized {s : ℂ} (hs : -2 < s.re) :
    riemannXi s = xiFactor s * regularizedPrincipal 1 s := by
  have hA : AnalyticOnNhd ℂ riemannXi {z : ℂ | -2 < z.re} :=
    fun z _ => differentiable_riemannXi.analyticAt z
  have hB : AnalyticOnNhd ℂ (fun z => xiFactor z * regularizedPrincipal 1 z)
      {z : ℂ | -2 < z.re} :=
    fun z hz => (analytic_xiFactor hz).mul (analytic_regularizedPrincipal 1 z)
  apply hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt (-2 : ℝ)).isPreconnected (z₀ := (2 : ℂ)) (by norm_num) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num : 1 < (2 : ℂ).re)] with z hz
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  rw [← Robin1984.completedZetaFactor_eq_riemannXi_of_one_lt_re hz,
    regularizedPrincipal_eq hz1, DirichletCharacter.LFunction_modOne_eq,
    Kadiri.completedZetaFactor, Kadiri.zetaPoleFactor, Kadiri.zetaGammaFactor,
    Robin1984.zetaPiFactor_eq_cpow_ascii, xiFactor]
  rw [show -(z / 2) = -z / 2 by ring]
  ring

theorem xi_eq_factor_regularized_nhds {s : ℂ} (hs : -2 < s.re) :
    riemannXi =ᶠ[𝓝 s] fun z => xiFactor z * regularizedPrincipal 1 z := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact xi_eq_factor_regularized hz

theorem analyticOrderAt_xi_eq_regularized {s : ℂ} (hs : -2 < s.re) :
    analyticOrderAt riemannXi s = analyticOrderAt (regularizedPrincipal 1) s := by
  rw [analyticOrderAt_congr (xi_eq_factor_regularized_nhds hs)]
  change analyticOrderAt (xiFactor * regularizedPrincipal 1) s = _
  rw [analyticOrderAt_mul (analytic_xiFactor hs) (analytic_regularizedPrincipal 1 s),
    (analytic_xiFactor hs).analyticOrderAt_eq_zero.mpr (xiFactor_ne_zero hs), zero_add]

theorem analyticOrderNatAt_xi_eq_regularized {s : ℂ} (hs : -2 < s.re) :
    analyticOrderNatAt riemannXi s = analyticOrderNatAt (regularizedPrincipal 1) s := by
  simp only [analyticOrderNatAt, analyticOrderAt_xi_eq_regularized hs]

theorem analyticOrderNatAt_xi_eq_principal {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderNatAt riemannXi s =
      analyticOrderNatAt (1 : DirichletCharacter ℂ q).LFunction s := by
  rw [analyticOrderNatAt_xi_eq_regularized (by linarith),
    analyticOrderNatAt_regularized_eq_principal hs1,
    DirichletCharacter.LFunction_modOne_eq,
    analyticOrderNatAt_principal_eq_zeta hs hs1]

theorem xi_zero_iff_regularized_zero {s : ℂ} (hs : -2 < s.re) :
    riemannXi s = 0 ↔ regularizedPrincipal 1 s = 0 := by
  rw [xi_eq_factor_regularized hs, mul_eq_zero]
  simp only [xiFactor_ne_zero hs, false_or]

theorem xi_zero_iff_zeta_zero {s : ℂ} (hs : -2 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [xi_zero_iff_regularized_zero hs, regularizedPrincipal_eq hs1,
    DirichletCharacter.LFunction_modOne_eq, mul_eq_zero]
  simp only [sub_ne_zero.mpr hs1, false_or]

theorem zeta_zero_strip {s : ℂ} (hs : -2 < s.re) (hz : riemannZeta s = 0) :
    0 < s.re ∧ s.re < 1 := by
  have hs1 : s ≠ 1 := by intro h; exact riemannZeta_one_ne_zero (h ▸ hz)
  have hxi := (xi_zero_iff_zeta_zero hs hs1).mpr hz
  have hs0 : s ≠ 0 := by intro h; simp [h, riemannZeta_zero] at hz
  obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    differentiable_riemannXi riemannXi_nontrivial hs0 hxi
  exact hp ▸ BombieriVinogradov.SiegelWalfisz.riemannXiDivisorZeroValue_re_mem_Ioo p

theorem zeta_ne_zero_left {s : ℂ} (hs : s.re = -1 / 2) : riemannZeta s ≠ 0 := by
  intro hz
  have h := (zeta_zero_strip (by linarith) hz).1
  linarith

end LiuWang.Proof.PrincipalPsi.Quantitative
