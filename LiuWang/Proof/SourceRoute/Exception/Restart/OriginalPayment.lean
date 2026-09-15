import LiuWang.Proof.SourceRoute.Exception.Restart.RealSources

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem two_zero_budget_contradiction {x beta gamma : ℝ} (hx : 10 ≤ x)
    (hb1 : beta < 1) (hg1 : gamma < 1)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hg : 1 - 1 / (9.645908801 * Real.log x) ≤ gamma)
    (hcore : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 23 / 20 →
      1 / (sigma - beta) + 1 / (sigma - gamma) ≤
        1 / (sigma - 1) + 4 * stechkinConductorCoeff * Real.log x) : False := by
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / (8 * Real.log x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  let u := (3 / 10) / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3 / 20 := by
    dsimp [u]
    apply (div_le_iff₀ hL0).mpr
    linarith
  have huL : u * Real.log x = 3 / 10 := by dsimp [u]; field_simp
  have hh := hcore (1 + u) (by linarith) (by linarith)
  have hinv : 1 / (1 + u - 1) = (10 / 3) * Real.log x := by
    dsimp [u]; field_simp; ring
  rw [hinv] at hh
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : 1 - b ≤ 1 / (8 * Real.log x)) :
      (40 / 17) * Real.log x ≤ 1 / (1 + u - b) := by
    have hh := (le_div_iff₀ (show 0 < 8 * Real.log x by positivity)).mp hgap
    apply (le_div_iff₀ (show 0 < 1 + u - b by linarith)).mpr
    nlinarith only [hh, huL]
  have h1 := hterm beta hb1 (by linarith)
  have h2 := hterm gamma hg1 (by linarith)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  nlinarith only [hh, h1, h2, hk, hL0]

end LiuWang.Proof.SourceRoute.Exception.Restart
