import LiuWang.Proof.Campaign20260915.Totient.RSLaplace
import LiuWang.Proof.Campaign20260915.Totient.RSParameters

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rs_theorem28_correction {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L) :
    rsLaplaceCorrection m (L / rsR) (Real.log (2 * Real.pi)) (999 / 100) ≤
      (m + 0.123) * L / (1748 * m ^ 2) := by
  have hR := rsR_pos
  have hc := rs_original_integral_constants
  have hb0 := hc.1
  have hscale := rs_original_scale_bounds.1
  have hfirst : (L / rsR) / (m * (999 / 100) ^ 2) ≤ L / (1748 * m) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hL (by positivity)
    nlinarith
  have hrec : 1 / (m * (999 / 100 - Real.log (2 * Real.pi))) ≤ 0.123 / m := by
    have h := div_le_div_of_nonneg_right hc.2.1 hm.le
    simpa only [div_div, mul_comm] using h
  unfold rsLaplaceCorrection
  calc
    _ ≤ (L / (1748 * m)) * (1 + 0.123 / m) := by
      apply mul_le_mul hfirst (add_le_add_right hrec 1) <;> positivity
    _ = _ := by field_simp

theorem rs_theorem28_laplace_bound {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L)
    (hupper : L < 1748 * m ^ 2 / (m + 0.123)) :
    IntegrableOn (rsLaplace m (L / rsR) (Real.log (2 * Real.pi))) (Ioi (999 / 100)) ∧
      0.1592 * (∫ u in Ioi (999 / 100),
        rsLaplace m (L / rsR) (Real.log (2 * Real.pi)) u) ≤
      Real.exp (-m * (999 / 100) - L / 175) * (1.298 * m + 0.1592) /
        ((1 - (m + 0.123) * L / (1748 * m ^ 2)) * m ^ 2) := by
  let r := rsLaplaceCorrection m (L / rsR) (Real.log (2 * Real.pi)) (999 / 100)
  let s := (m + 0.123) * L / (1748 * m ^ 2)
  have hR := rsR_pos
  have hconstants := rs_original_integral_constants
  have hb0 := hconstants.1
  have hs : s < 1 := by
    apply (div_lt_one (by positivity : 0 < 1748 * m ^ 2)).mpr
    have h := (lt_div_iff₀ (by linarith : 0 < m + 0.123)).mp hupper
    nlinarith
  have hrs : r ≤ s := rs_theorem28_correction hm hL
  have hr : r < 1 := hrs.trans_lt hs
  have hi := rsLaplace_integral_le hm (div_nonneg hL hR.le)
    (by norm_num : (0 : ℝ) < 999 / 100)
    (by linarith [hconstants.1] : Real.log (2 * Real.pi) < 999 / 100) hr
  refine ⟨hi.1, ?_⟩
  have hP : 0 ≤ rsLaplacePrimitive m (L / rsR) (Real.log (2 * Real.pi)) (999 / 100) := by
    unfold rsLaplacePrimitive
    positivity
  have hdiv :
      rsLaplacePrimitive m (L / rsR) (Real.log (2 * Real.pi)) (999 / 100) / (1 - r) ≤
      rsLaplacePrimitive m (L / rsR) (Real.log (2 * Real.pi)) (999 / 100) / (1 - s) :=
    div_le_div_of_nonneg_left hP (by linarith) (by linarith)
  have he : Real.exp (-m * (999 / 100) - (L / rsR) / (999 / 100)) ≤
      Real.exp (-m * (999 / 100) - L / 175) := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_left hL
      (mul_pos hR (by norm_num : (0 : ℝ) < 999 / 100)) rs_original_scale_bounds.2
    rw [div_div]
    linarith
  have hn : 0.1592 * (((999 / 100) - Real.log (2 * Real.pi)) / m + 1 / m ^ 2) ≤
      (1.298 * m + 0.1592) / m ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hconstants.2.2 hm.le
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    field_simp
    nlinarith
  calc
    _ ≤ (0.1592 * rsLaplacePrimitive m (L / rsR) (Real.log (2 * Real.pi)) (999 / 100)) /
        (1 - s) := by
      have h := mul_le_mul_of_nonneg_left (hi.2.trans hdiv) (by norm_num : (0 : ℝ) ≤ 0.1592)
      simpa only [mul_div_assoc] using h
    _ ≤ (Real.exp (-m * (999 / 100) - L / 175) * ((1.298 * m + 0.1592) / m ^ 2)) /
        (1 - s) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      unfold rsLaplacePrimitive
      rw [mul_left_comm (0.1592 : ℝ)]
      exact mul_le_mul he hn (by positivity) (Real.exp_pos _).le
    _ = _ := by
      dsimp [s]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms rs_theorem28_correction
#print axioms rs_theorem28_laplace_bound

end LiuWang.Proof.Campaign20260915.Totient
