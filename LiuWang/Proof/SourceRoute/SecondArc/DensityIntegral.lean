import LiuWang.Proof.SourceRoute.SecondArc.AlphaIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem integral_exp_affine {k : ℝ} (hk : k ≠ 0) (a b H : ℝ) :
    (∫ alpha in a..b, H * Real.exp ((alpha - 1) * k)) =
      H / k * (Real.exp ((b - 1) * k) - Real.exp ((a - 1) * k)) := by
  have hd (alpha : ℝ) :
      HasDerivAt (fun t : ℝ => H / k * Real.exp ((t - 1) * k))
        (H * Real.exp ((alpha - 1) * k)) alpha := by
    convert! ((((hasDerivAt_id alpha).sub_const 1).mul_const k).exp.const_mul (H / k)) using 1
    field_simp
    simp only [id_eq, mul_comm]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun alpha _ => hd alpha)
    ((by fun_prop : Continuous (fun alpha : ℝ => H * Real.exp ((alpha - 1) * k))).intervalIntegrable a b)]
  ring

theorem integral_exp_density_cap {k : ℝ} (hk : k ≠ 0) (a H c z : ℝ) :
    (∫ alpha in a..(1 - c / z), H * Real.exp ((alpha - 1) * k)) =
      H / k * (Real.exp (-c * k / z) - Real.exp ((a - 1) * k)) := by
  rw [integral_exp_affine hk]
  congr 2
  congr 1
  ring

theorem integral_exp_density_cap_le {k H : ℝ} (hk : 0 < k) (hH : 0 ≤ H)
    (a c z : ℝ) :
    (∫ alpha in a..(1 - c / z), H * Real.exp ((alpha - 1) * k)) ≤
      H / k * Real.exp (-c * k / z) := by
  rw [integral_exp_density_cap hk.ne']
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) (div_nonneg hH hk.le)

/-- Exact integration of the two near-one strips in (5.15)--(5.17). -/
theorem integral_alpha_strip {x : ℝ} (hx : 0 < x) (c d z : ℝ) :
    (∫ alpha in (1 - c / z)..(1 - d / z), alphaKernel x alpha) =
      Real.exp (-d * Real.log x / z) - Real.exp (-c * Real.log x / z) := by
  rw [integral_alphaKernel hx]
  simp only [Real.rpow_def_of_pos hx]
  congr 1 <;> congr 1 <;> ring

theorem source_515_first_strip {x : ℝ} (hx : 0 < x) (z : ℝ) :
    (∫ alpha in (1 - (0.478 : ℝ) / z)..(1 - (0.2067 : ℝ) / z),
      alphaKernel x alpha) =
      Real.exp (-0.2067 * Real.log x / z) - Real.exp (-0.478 * Real.log x / z) :=
  integral_alpha_strip hx _ _ _

theorem source_515_last_strip {x : ℝ} (hx : 0 < x) (z c₁ : ℝ) :
    (∫ alpha in (1 - (0.2067 : ℝ) / z)..(1 - 1 / (c₁ * z)),
      alphaKernel x alpha) =
      Real.exp (-(1 / c₁) * Real.log x / z) -
        Real.exp (-0.2067 * Real.log x / z) := by
  rw [show 1 / (c₁ * z) = (1 / c₁) / z by ring]
  exact integral_alpha_strip hx _ _ _

theorem density_cap_exponent (H c z : ℝ) (hz : z ≠ 0) :
    Real.exp (-c * (H - 4 * z) / z) =
      Real.exp (4 * c) * Real.exp (-c * H / z) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

theorem density_cap_integral_le {H z : ℝ} (hz : 0 < z) (hH : 4 * z < H)
    (a c : ℝ) :
    (∫ alpha in a..(1 - c / z), H * Real.exp ((alpha - 1) * (H - 4 * z))) ≤
      Real.exp (4 * c) * (H / (H - 4 * z)) * Real.exp (-c * H / z) := by
  have hb := integral_exp_density_cap_le (by linarith : 0 < H - 4 * z)
    (by linarith : 0 ≤ H) a c z
  rw [density_cap_exponent H c z hz.ne'] at hb
  exact hb.trans_eq (by ring)

end LiuWang.Proof.SourceRoute.SecondArc
