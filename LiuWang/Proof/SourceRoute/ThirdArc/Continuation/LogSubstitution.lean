import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TableIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The original logarithmic height substitution, without a continuity assumption on counts. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

theorem exp_div_substitution {q u v : ℝ} (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (F : ℝ → ℝ) :
    (∫ y in u..v, F y) =
      ∫ t in Real.log (q * u)..Real.log (q * v),
        F (Real.exp t / q) * (Real.exp t / q) := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun t => Real.exp t / q) (f' := fun t => Real.exp t / q)
    (g := F) (a := Real.log (q * u)) (b := Real.log (q * v))
    (Real.continuous_exp.div_const q).continuousOn
    (fun t _ => (Real.hasDerivAt_exp t).div_const q)
    (fun t _ => (div_pos (Real.exp_pos t) hq).le)
  have he (x : ℝ) (hx : 0 < x) : Real.exp (Real.log (q * x)) / q = x := by
    rw [Real.exp_log (mul_pos hq hx)]
    field_simp
  simpa only [Function.comp_apply, he u hu, he v hv] using h.symm

theorem heightKernel_exp_jacobian {q : ℝ} (hq : 0 < q) (p t : ℝ) :
    heightKernel p (Real.exp t / q) * (Real.exp t / q) =
      p * q ^ p * Real.exp (-p * t) := by
  have hy : 0 < Real.exp t / q := div_pos (Real.exp_pos t) hq
  have hp : (Real.exp t / q) ^ (-p - 1) * (Real.exp t / q) =
      (Real.exp t / q) ^ (-p) := by
    rw [← Real.rpow_add_one hy.ne']
    congr 1
    ring
  rw [heightKernel, mul_assoc, hp, Real.div_rpow (Real.exp_pos t).le hq.le,
    Real.rpow_neg hq.le, div_inv_eq_mul, ← Real.exp_mul]
  rw [mul_comm t (-p)]
  ring

theorem height_log_substitution {q u v : ℝ} (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (p : ℝ) (F : ℝ → ℝ) :
    (∫ y in u..v, heightKernel p y * F y) =
      p * q ^ p * ∫ t in Real.log (q * u)..Real.log (q * v),
        Real.exp (-p * t) * F (Real.exp t / q) := by
  rw [exp_div_substitution hq hu hv, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  calc
    _ = (heightKernel p (Real.exp t / q) * (Real.exp t / q)) * F (Real.exp t / q) := by ring
    _ = _ := by rw [heightKernel_exp_jacobian hq]; ring

theorem countIntegral_log_substitution (q : ℕ) [NeZero q] {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (X a b p : ℝ) :
    (∫ y in u..v, heightKernel p y * countIntegral q X y a b) =
      p * (q : ℝ) ^ p * ∫ t in Real.log ((q : ℝ) * u)..Real.log ((q : ℝ) * v),
        Real.exp (-p * t) * countIntegral q X (Real.exp t / q) a b := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  exact height_log_substitution hq hu hv p _

theorem moving_countIntegral_log_substitution (q : ℕ) [NeZero q] {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (X a d p : ℝ) :
    (∫ y in u..v, heightKernel p y *
        countIntegral q X y a (1 - d / Real.log ((q : ℝ) * y))) =
      p * (q : ℝ) ^ p * ∫ t in Real.log ((q : ℝ) * u)..Real.log ((q : ℝ) * v),
        Real.exp (-p * t) * countIntegral q X (Real.exp t / q) a (1 - d / t) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  rw [height_log_substitution hq hu hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have he : (q : ℝ) * (Real.exp t / q) = Real.exp t := by field_simp
  rw [he, Real.log_exp]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
