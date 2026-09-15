import LiuWang.Proof.Campaign20260915.Totient.RSTheorem28Integral
import LiuWang.Proof.Campaign20260915.Totient.RSHighZeros

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_phi_exp_change (m : ℕ) (L u : ℝ) :
    Real.exp u * (rsPhi m L (Real.exp u) * Real.log (Real.exp u / (2 * Real.pi))) =
      rsLaplace m (L / rsR) (Real.log (2 * Real.pi)) u := by
  have hex : Real.exp (-(m : ℝ) * u - (L / rsR) / u) =
      Real.exp (-(L / (rsR * u))) / Real.exp u ^ m := by
    rw [div_div, show -(m : ℝ) * u - L / (rsR * u) =
      -(L / (rsR * u)) - (m : ℝ) * u by ring,
      Real.exp_sub, Real.exp_nat_mul]
  unfold rsPhi rsLaplace
  rw [Real.log_exp, Real.log_div (Real.exp_ne_zero u) (by positivity),
    Real.log_exp, hex, pow_succ]
  field_simp

theorem rs_phi_integral_original {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (hupper : L < 1748 * (m : ℝ) ^ 2 / ((m : ℝ) + 0.123)) :
    IntegrableOn (fun t => rsPhi m L t * Real.log (t / (2 * Real.pi))) (Ioi rsA) ∧
      0.1592 * (∫ t in Ioi rsA, rsPhi m L t * Real.log (t / (2 * Real.pi))) ≤
        (1.298 * (m : ℝ) + 0.1592) /
          ((1 - ((m : ℝ) + 0.123) * L / (1748 * (m : ℝ) ^ 2)) *
            (m : ℝ) ^ 2 * rsA ^ m * Real.exp (L / 175)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hi := rs_theorem28_laplace_bound hm0 hL hupper
  have hfun : (fun u => Real.exp u •
      (rsPhi m L (Real.exp u) * Real.log (Real.exp u / (2 * Real.pi)))) =
      rsLaplace m (L / rsR) (Real.log (2 * Real.pi)) := by
    funext u
    exact rs_phi_exp_change m L u
  have hchange := integral_comp_exp_Ioi
    (fun t => rsPhi m L t * Real.log (t / (2 * Real.pi))) (999 / 100)
  rw [hfun] at hchange
  have hiff := integrableOn_comp_exp_Ioi
    (fun t => rsPhi m L t * Real.log (t / (2 * Real.pi))) (999 / 100)
  rw [hfun] at hiff
  rw [show Real.exp (999 / 100) = rsA from rfl] at hchange hiff
  refine ⟨hiff.mp hi.1, ?_⟩
  rw [← hchange]
  apply hi.2.trans_eq
  have he : Real.exp (-(m : ℝ) * (999 / 100) - L / 175) =
      1 / (rsA ^ m * Real.exp (L / 175)) := by
    rw [show -(m : ℝ) * (999 / 100) - L / 175 =
      -((m : ℝ) * (999 / 100) + L / 175) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_nat_mul]
    simp only [rsA, one_div]
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms rs_phi_integral_original

end LiuWang.Proof.Campaign20260915.Totient
