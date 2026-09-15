import LiuWang.Proof.NearOneDensity.DirichletKernel

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace LiuWang.Proof.NearOneDensity

theorem mangoldt_mass_eq_zeta {σ : ℝ} (hσ : 1 < σ) :
    (∑' n, mangoldtWeight σ n) =
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (show 1 < (σ : ℂ).re by simpa using hσ)]
  rw [LSeries, Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < (σ : ℂ).re by simpa using hσ))]
  exact tsum_congr (fun n => by rw [← ofReal_mangoldtWeight, Complex.ofReal_re])

theorem damped_mass_eq_zeta {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    (∑' n, dampedWeight σ τ c n) =
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re -
        c * (-deriv riemannZeta (τ : ℂ) / riemannZeta (τ : ℂ)).re := by
  simp only [dampedWeight]
  rw [(summable_mangoldtWeight hσ).tsum_sub
    ((summable_mangoldtWeight hτ).mul_left c), tsum_mul_left,
    mangoldt_mass_eq_zeta hσ, mangoldt_mass_eq_zeta hτ]

theorem logKernel_bounds_by_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    -(∑' n, dampedWeight σ τ c n) ≤ logKernel σ τ c χ t ∧
      logKernel σ τ c χ t ≤ ∑' n, dampedWeight σ τ c n := by
  rw [logKernel_eq_series χ t hσ hτ]
  have hs := summable_weight_phase_re χ t (c := c) hσ hτ
  have hw := summable_dampedWeight (c := c) hσ hτ
  have hp (n : ℕ) : |(phase χ t n).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (norm_phase_le_one χ t n)
  constructor
  · rw [← tsum_neg]
    apply hw.neg.tsum_le_tsum _ hs
    intro n
    have h := mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hp n)) (dampedWeight_nonneg hστ hc n)
    simpa only [mul_neg, mul_one] using h
  · apply hs.tsum_le_tsum _ hw
    intro n
    exact mul_le_of_le_one_right (dampedWeight_nonneg hστ hc n) (le_of_abs_le (hp n))

theorem logKernel_add_zeta_mass_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    {σ τ c : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) (hστ : σ ≤ τ) (hc : c ≤ 1) :
    0 ≤ logKernel σ τ c χ t +
      ((-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re -
        c * (-deriv riemannZeta (τ : ℂ) / riemannZeta (τ : ℂ)).re) := by
  rw [← damped_mass_eq_zeta hσ hτ]
  linarith [(logKernel_bounds_by_mass χ t hσ hτ hστ hc).1]

end LiuWang.Proof.NearOneDensity
