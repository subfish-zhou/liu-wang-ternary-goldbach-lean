import LiuWang.Proof.ZeroRegionFamily.Family
import LiuWang.Proof.ZeroRegionFamily.StechkinKernel

/-! # 实际已付的有限区域消费者；原9.645908801区域不在本模块的结论内 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.ZeroRegionFamily

theorem quadratic_values_real {q : ℕ} (chi : DirichletCharacter ℂ q) (hs : chi^2=1)
    (n : ZMod q) : (chi n).im=0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hs n with h | h | h <;> simp [h]

theorem single_modulus_weak {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) :
    Subsingleton (countedZeros x q) ∧
      ∀ (chi : DirichletCharacter ℂ q) (rho : ℂ),
        1-1/(2560*Real.log x) < rho.re → |rho.im| ≤ x/(q : ℝ) →
        (chi ≠ 1 ∨ rho ≠ 1) → chi.LFunction rho=0 →
        chi ≠ 1 ∧ (∀ n : ZMod q, (chi n).im=0) ∧
          rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 := by
  refine ⟨countedZeros_subsingleton hx hq, ?_⟩
  intro chi rho hre him hp hz
  obtain ⟨hc, hs, hr, hm⟩ := weak_zero_real_quadratic_simple hx hq chi ⟨hre, him⟩ hp hz
  exact ⟨hc, quadratic_values_real chi hs, hr, hm⟩

theorem family_weak_from_actual_zero {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (hre : 1-1/(2560*Real.log x) < rho.re)
    (him : |rho.im| ≤ x/(q : ℝ))
    (hp : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho=0) :
    ∃ d : PrimitiveQuadraticDatum, (d.modulus : ℝ) ≤ x ∧
      d.modulus=chi.conductor ∧ inducedAt d q=chi ∧ datumL d rho=0 ∧
      rho.im=0 ∧ analyticOrderNatAt chi.LFunction rho=1 ∧
      ∀ (r : ℕ) [NeZero r], (r : ℝ) ≤ x →
        ∀ (psi : DirichletCharacter ℂ r) (tau : ℂ),
          1-1/(2560*Real.log x) < tau.re → |tau.im| ≤ x/(r : ℝ) →
          (psi ≠ 1 ∨ tau ≠ 1) → psi.LFunction tau=0 →
            tau=rho ∧ d.modulus=psi.conductor ∧ d.modulus ∣ r ∧
              inducedAt d r=psi ∧ analyticOrderNatAt psi.LFunction tau=1 := by
  obtain ⟨d, hd, hdc, hdi, hdz, hr, hm, hall⟩ :=
    weak_family_fixed_source hx hq chi ⟨hre, him⟩ hp hz
  refine ⟨d, hd, hdc, hdi, hdz, hr, hm, ?_⟩
  intro r _ hrq psi tau htre htim htp htz
  exact hall r hrq psi tau ⟨htre, htim⟩ htp htz

theorem modulus_one_no_weak_zero {x : ℝ} (hx : 10 ≤ x)
    (chi : DirichletCharacter ℂ 1) {rho : ℂ}
    (hr : 1-1/(2560*Real.log x) < rho.re) (hi : |rho.im| ≤ x)
    (hp : rho ≠ 1) : chi.LFunction rho ≠ 0 := by
  have hc : chi=1 := Subsingleton.elim _ _
  subst chi
  exact principal_no_weak_zero hx (by norm_num; linarith) ⟨hr, by simpa using hi⟩ hp

theorem stechkin_actual_zero_selected {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hc : chi ≠ 1) (hp : chi.IsPrimitive)
    {rho : ℂ} (hr : 1/2 < rho.re) (hz : chi.LFunction rho=0)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t+
      dampedZeroKernel sigma t rho+
      dampedZeroKernel sigma t (1-(starRingEnd ℂ) rho) ≤
      (1-stechkinK)*Real.log q/2+
      (logDeriv chi.gammaFactor ((sigma : ℂ)+Complex.I*t)).re-
      stechkinK*(logDeriv chi.gammaFactor ((stechkinSigma sigma : ℂ)+Complex.I*t)).re := by
  obtain ⟨p, hv⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hc hp (by linarith) hz
  have hsel := damped_selected_pair_le hc hp hs t p (by simpa only [hv] using hr)
  rw [hv] at hsel
  have hid := damped_kernel_identity hc hp hs (hs.trans_le (stechkinSigma_ge hs)) stechkinK t
  dsimp [dampedZeroKernel] at hsel ⊢
  linarith

end LiuWang.Proof.ZeroRegionFamily
