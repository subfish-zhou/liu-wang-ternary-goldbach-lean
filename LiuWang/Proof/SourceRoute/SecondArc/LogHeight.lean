import LiuWang.Proof.SourceRoute.SecondArc.DensityIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem log_height_jacobian {q : ℝ} (hq : 0 < q) (z : ℝ) :
    (Real.exp z / q) * heightKernel (Real.exp z / q) =
      Real.sqrt q * Real.exp (-z / 2) := by
  have he : Real.exp z / q = Real.exp (z - Real.log q) := by
    rw [Real.exp_sub, Real.exp_log hq]
  rw [he, heightKernel, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq, ← Real.exp_add]
  congr 1
  ring

/-- The exact height substitution in (5.9), (5.16), and (5.17). -/
theorem log_height_change {q u v : ℝ} (hq : 0 < q) (hu : 0 < u)
    (hv : 0 < v) (F : ℝ → ℝ) :
    (∫ y in u..v, heightKernel y * F (Real.log (q * y))) =
      Real.sqrt q * ∫ z in Real.log (q * u)..Real.log (q * v),
        Real.exp (-z / 2) * F z := by
  have hd (z : ℝ) :
      HasDerivAt (fun t : ℝ => Real.exp t / q) (Real.exp z / q) z :=
    (Real.hasDerivAt_exp z).div_const q
  have he (w : ℝ) (hw : 0 < w) : Real.exp (Real.log (q * w)) / q = w := by
    rw [Real.exp_log (mul_pos hq hw)]
    field_simp
  have hs := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := Real.log (q * u)) (b := Real.log (q * v))
    (f := fun z : ℝ => Real.exp z / q) (f' := fun z : ℝ => Real.exp z / q)
    (g := fun y : ℝ => heightKernel y * F (Real.log (q * y)))
    (by fun_prop) (fun z _ => hd z) (fun z _ => div_nonneg (Real.exp_pos z).le hq.le)
  rw [he u hu, he v hv] at hs
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only [Function.comp_def, smul_eq_mul]
  have hlog : Real.log (q * (Real.exp z / q)) = z := by
    rw [mul_div_cancel₀ _ hq.ne', Real.log_exp]
  rw [hlog, ← mul_assoc, log_height_jacobian hq]
  ring

theorem normalized_log_height_change {q phi u v : ℝ}
    (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) (F : ℝ → ℝ) :
    (Real.sqrt q / phi) * (∫ y in u..v, heightKernel y * F (Real.log (q * y))) =
      (q / phi) * ∫ z in Real.log (q * u)..Real.log (q * v),
        Real.exp (-z / 2) * F z := by
  rw [log_height_change hq hu hv F]
  calc
    _ = (Real.sqrt q * Real.sqrt q) / phi *
        ∫ z in Real.log (q * u)..Real.log (q * v), Real.exp (-z / 2) * F z := by ring
    _ = _ := by rw [Real.mul_self_sqrt hq.le]

theorem log_height_source_endpoints {q L : ℝ} (hq : 0 < q) :
    Real.log (q * (3.36 * L ^ (3 : ℕ) / q)) = Real.log (3.36 * L ^ (3 : ℕ)) ∧
      Real.log (q * (10 * Real.pi * L ^ (7 : ℕ) / q)) =
        Real.log (10 * Real.pi * L ^ (7 : ℕ)) := by
  constructor <;> congr 1 <;> field_simp

theorem source_516_log_integral {q phi x u v : ℝ}
    (hq : 0 < q) (hx : 0 < x) (hu : 0 < u) (hv : 0 < v) :
    (Real.sqrt q / phi) *
      (∫ y in u..v, heightKernel y *
        ∫ alpha in (1 - (0.478 : ℝ) / Real.log (q * y))..
          (1 - (0.2067 : ℝ) / Real.log (q * y)), alphaKernel x alpha) =
      (q / phi) * ∫ z in Real.log (q * u)..Real.log (q * v),
        Real.exp (-z / 2) *
          (Real.exp (-0.2067 * Real.log x / z) -
            Real.exp (-0.478 * Real.log x / z)) := by
  simp_rw [source_515_first_strip hx]
  exact normalized_log_height_change (phi := phi) hq hu hv
    (fun z => Real.exp (-0.2067 * Real.log x / z) - Real.exp (-0.478 * Real.log x / z))

theorem source_517_log_integral {q phi x u v : ℝ}
    (hq : 0 < q) (hx : 0 < x) (hu : 0 < u) (hv : 0 < v) (c₁ : ℝ) :
    (Real.sqrt q / phi) *
      (∫ y in u..v, heightKernel y *
        ∫ alpha in (1 - (0.2067 : ℝ) / Real.log (q * y))..
          (1 - 1 / (c₁ * Real.log (q * y))), alphaKernel x alpha) =
      (q / phi) * ∫ z in Real.log (q * u)..Real.log (q * v),
        Real.exp (-z / 2) *
          (Real.exp (-(1 / c₁) * Real.log x / z) -
            Real.exp (-0.2067 * Real.log x / z)) := by
  simp_rw [source_515_last_strip hx]
  exact normalized_log_height_change (phi := phi) hq hu hv
    (fun z => Real.exp (-(1 / c₁) * Real.log x / z) - Real.exp (-0.2067 * Real.log x / z))

end LiuWang.Proof.SourceRoute.SecondArc
