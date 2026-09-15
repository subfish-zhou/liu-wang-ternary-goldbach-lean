import LiuWang.Proof.SourceRoute.Exception.Restart.Family

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem original_seed_lifetime {x beta : ℝ} (hx : 10 ≤ x) (hb : beta < 1) :
    1 - 1 / (9.645908801 * Real.log x) ≤ beta ↔
      Real.log x ≤ 1 / (9.645908801 * (1 - beta)) := by
  have hL := log_scale_ge hx
  have hp : 0 < 9.645908801 * Real.log x := by positivity
  have hb0 : 0 < 9.645908801 * (1 - beta) := by positivity
  rw [le_div_iff₀ hb0]
  constructor
  · intro hh
    have h := (le_div_iff₀ hp).mp (show 1 - beta ≤ 1 / (9.645908801 * Real.log x) by linarith)
    nlinarith only [h]
  · intro hh
    have h : 1 - beta ≤ 1 / (9.645908801 * Real.log x) := (le_div_iff₀ hp).mpr (by nlinarith only [hh])
    linarith

theorem moving_fixed_source_characterization (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] {y beta : ℝ} (hy : 1 ≤ y) (hscale : 10 ≤ (q : ℝ) * y)
    (hd : (d.modulus : ℝ) ≤ (q : ℝ) * y)
    (hb : 1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) ≤ rho.re)
    (ht : |rho.im| ≤ y) (hpole : chi ≠ 1 ∨ rho ≠ 1) (hz : chi.LFunction rho = 0) :
    chi ≠ 1 ∧ d.modulus = chi.conductor ∧ d.modulus ∣ q ∧
      chi = inducedAt d q ∧ rho = (beta : ℂ) ∧ analyticOrderNatAt chi.LFunction rho = 1 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq : (q : ℝ) ≤ (q : ℝ) * y := by nlinarith
  have hheight : |rho.im| ≤ ((q : ℝ) * y) / q := by
    simpa only [mul_div_cancel_left₀ y (ne_of_gt hq0)] using ht
  exact fixed_source_characterization d hscale hd hb hzb hq chi hr hheight hpole hz

theorem moving_noninducing_no_zero (d : PrimitiveQuadraticDatum)
    {q : ℕ} [NeZero q] {y beta : ℝ} (hy : 1 ≤ y) (hscale : 10 ≤ (q : ℝ) * y)
    (hd : (d.modulus : ℝ) ≤ (q : ℝ) * y) (hdq : ¬d.modulus ∣ q)
    (hb : 1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hr : 1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) ≤ rho.re)
    (ht : |rho.im| ≤ y) (hpole : chi ≠ 1 ∨ rho ≠ 1) : chi.LFunction rho ≠ 0 :=
  fun hz => hdq (moving_fixed_source_characterization d hy hscale hd hb hzb chi hr ht hpole hz).2.2.1

end LiuWang.Proof.SourceRoute.Exception.Restart
