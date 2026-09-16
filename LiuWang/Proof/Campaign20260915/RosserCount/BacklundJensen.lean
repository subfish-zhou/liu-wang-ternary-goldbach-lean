import LiuWang.Proof.Campaign20260915.RosserCount.BacklundCenter
import Mathlib.Analysis.Complex.JensenFormula

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open Complex Filter Metric MeasureTheory MeromorphicOn Real
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.RosserCount

open LiuWang.Proof.Campaign20260915.Totient

theorem backlundAux_analyticOnNhd {T : ℝ} (hT : rsA ≤ T) (n : ℕ) :
    AnalyticOnNhd ℂ (backlundAux T n) (closedBall 0 (33 / 25 : ℝ)) := by
  intro s hs
  have hs' : ‖s‖ ≤ (33 / 25 : ℝ) := by simpa using hs
  have hi := (abs_le.mp ((abs_im_le_norm s).trans hs'))
  have hplus : s + 5 / 4 + (T : ℂ) * I ≠ 1 := by
    intro he
    have he' := congrArg Complex.im he
    norm_num at he'
    linarith [rsA_ge_thousand]
  have hminus : s + 5 / 4 - (T : ℂ) * I ≠ 1 := by
    intro he
    have he' := congrArg Complex.im he
    norm_num at he'
    linarith [rsA_ge_thousand]
  have ha := (LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hplus).comp
    (f := fun z : ℂ => z + 5 / 4 + (T : ℂ) * I)
    (show AnalyticAt ℂ (fun z : ℂ => z + 5 / 4 + (T : ℂ) * I) s by fun_prop)
  have hb := (LiuWang.Proof.PrincipalPsi.analytic_zeta_of_ne_one hminus).comp
    (f := fun z : ℂ => z + 5 / 4 - (T : ℂ) * I)
    (show AnalyticAt ℂ (fun z : ℂ => z + 5 / 4 - (T : ℂ) * I) s by fun_prop)
  convert!
    ((ha.pow n).add (hb.pow n)).mul
      (show AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)⁻¹) s by fun_prop) using 1

theorem backlundAux_circleIntegrable_log_norm {T : ℝ} (hT : rsA ≤ T) (n : ℕ) :
    CircleIntegrable (fun s => Real.log ‖backlundAux T n s‖) 0 (33 / 25 : ℝ) := by
  apply MeromorphicOn.circleIntegrable_log_norm
  simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using
    ((backlundAux_analyticOnNhd hT n).mono sphere_subset_closedBall).meromorphicOn

theorem backlundAux_jensen_formula {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    circleAverage (fun s => Real.log ‖backlundAux T n s‖) 0 (33 / 25 : ℝ) =
      (∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ)) z : ℝ) *
        Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹)) + Real.log ‖backlundAux T n 0‖ := by
  have ha : AnalyticOnNhd ℂ (backlundAux T n) (closedBall 0 |(33 / 25 : ℝ)|) := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] using backlundAux_analyticOnNhd hT n
  have hj := ha.circleAverage_log_norm (by norm_num : (33 / 25 : ℝ) ≠ 0) hn
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 33 / 25)] at hj
  simpa only [zero_sub, norm_neg] using hj

theorem backlundAux_small_divisor_bound {T : ℝ} (hT : rsA ≤ T) {n : ℕ}
    (hn : backlundAux T n 0 ≠ 0) :
    (∑ᶠ z, (divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ)) z : ℝ)) ≤
      (circleAverage (fun s => Real.log ‖backlundAux T n s‖) 0 (33 / 25 : ℝ) -
        Real.log ‖backlundAux T n 0‖) / Real.log (44 / 25 : ℝ) := by
  let D := divisor (backlundAux T n) (closedBall 0 (33 / 25 : ℝ))
  let d := divisor (backlundAux T n) (closedBall 0 (3 / 4 : ℝ))
  have ha := backlundAux_analyticOnNhd hT n
  have hb : AnalyticOnNhd ℂ (backlundAux T n) (closedBall 0 (3 / 4 : ℝ)) :=
    ha.mono (closedBall_subset_closedBall (by norm_num))
  have hq : 0 < Real.log (44 / 25 : ℝ) := Real.log_pos (by norm_num)
  have hD (z : ℂ) : (0 : ℝ) ≤ D z := by exact_mod_cast ha.divisor_nonneg z
  have hd0 : d 0 = 0 := by
    dsimp [d]
    rw [hb.divisor_apply (by norm_num), (hb 0 (by norm_num)).analyticOrderAt_eq_zero.mpr hn]
    simp
  have hD0 : D 0 = 0 := by
    dsimp [D]
    rw [ha.divisor_apply (by norm_num), (ha 0 (by norm_num)).analyticOrderAt_eq_zero.mpr hn]
    simp
  have hpoint (z : ℂ) :
      (d z : ℝ) * Real.log (44 / 25 : ℝ) ≤
        (D z : ℝ) * Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹) := by
    by_cases hR : z ∈ closedBall 0 (33 / 25 : ℝ)
    · by_cases hz : z = 0
      · subst z
        simp [hd0, hD0]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hR' : ‖z‖ ≤ (33 / 25 : ℝ) := by simpa using hR
      by_cases hr : z ∈ closedBall 0 (3 / 4 : ℝ)
      · have he : d z = D z := by
          dsimp [d, D]
          rw [hb.divisor_apply hr, ha.divisor_apply hR]
        rw [he]
        apply mul_le_mul_of_nonneg_left _ (hD z)
        apply Real.log_le_log (by norm_num)
        rw [← div_eq_mul_inv, le_div_iff₀ hz0]
        have hr' : ‖z‖ ≤ (3 / 4 : ℝ) := by simpa using hr
        linarith
      · have he : d z = 0 := by simp [d, hr]
        rw [he, Int.cast_zero, zero_mul]
        apply mul_nonneg (hD z)
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ hz0]
        simpa using hR'
    · have hr : z ∉ closedBall 0 (3 / 4 : ℝ) :=
        fun h => hR (closedBall_subset_closedBall (by norm_num) h)
      simp [d, D, hR, hr]
  have hsum :
      (∑ᶠ z, (d z : ℝ) * Real.log (44 / 25 : ℝ)) ≤
        ∑ᶠ z, (D z : ℝ) * Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹) := by
    refine finsum_le_finsum' ?_ ?_ hpoint
    · exact (d.finiteSupport (isCompact_closedBall ..)).subset (fun _ _ => by simp_all)
    · exact (D.finiteSupport (isCompact_closedBall ..)).subset (fun _ _ => by simp_all)
  rw [← finsum_mul] at hsum
  apply (le_div_iff₀ hq).mpr
  have hj := backlundAux_jensen_formula hT hn
  change _ = (∑ᶠ z, (D z : ℝ) * Real.log ((33 / 25 : ℝ) * ‖z‖⁻¹)) +
    Real.log ‖backlundAux T n 0‖ at hj
  change (∑ᶠ z, (d z : ℝ)) * Real.log (44 / 25 : ℝ) ≤ _
  linarith

theorem backlundAux_jensen_sequence {T : ℝ} (hT : rsA ≤ T) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      Tendsto (fun n => Real.log ‖backlundAux T (f n) 0‖ / (f n : ℝ))
        atTop (𝓝 (Real.log ‖riemannZeta (backlundCenterPoint T)‖)) ∧
      ∀ n, (∑ᶠ z, (divisor (backlundAux T (f n)) (closedBall 0 (3 / 4 : ℝ)) z : ℝ)) ≤
        (circleAverage (fun s => Real.log ‖backlundAux T (f n) s‖) 0 (33 / 25 : ℝ) -
          Real.log ‖backlundAux T (f n) 0‖) / Real.log (44 / 25 : ℝ) := by
  obtain ⟨f, hf, hn, hl⟩ := backlundAux_center_log_limit T
  exact ⟨f, hf, hl, fun n => backlundAux_small_divisor_bound hT (hn n)⟩

#print axioms backlundAux_analyticOnNhd
#print axioms backlundAux_circleIntegrable_log_norm
#print axioms backlundAux_jensen_formula
#print axioms backlundAux_small_divisor_bound
#print axioms backlundAux_jensen_sequence

end LiuWang.Proof.Campaign20260915.RosserCount
