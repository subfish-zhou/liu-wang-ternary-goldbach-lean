import LiuWang.Proof.ZeroRegionFamily.Sharp.ZeroSumBudget

/-! # 无未付解析前提的普通L消费者；R20不是原R9.645908801 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

theorem ordinary_region_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hbranch : chi^2 ≠ 1 ∨ 1/2 ≤ |rho.im|) : chi.LFunction rho ≠ 0 := by
  rcases hbranch with hsq | hlo
  · exact nonquadratic_no_zero_twenty hx hq chi hsq hr ht
  · exact nonprincipal_high_no_zero_twenty hx hq chi hc hr hlo ht

theorem ordinary_zero_localized_twenty {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 10 ≤ x) (hq : (q : ℝ) ≤ x) (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {rho : ℂ} (hr : 1-1/(20*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ))
    (hz : chi.LFunction rho=0) : chi^2=1 ∧ |rho.im| < 1/2 := by
  constructor
  · by_contra hsq
    exact ordinary_region_twenty hx hq chi hc hr ht (Or.inl hsq) hz
  · by_contra hlo
    exact ordinary_region_twenty hx hq chi hc hr ht (Or.inr (le_of_not_gt hlo)) hz

end LiuWang.Proof.ZeroRegionFamily.Sharp
