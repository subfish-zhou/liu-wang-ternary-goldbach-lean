import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ScalarDomain
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation

def originalKernel (L z : ℝ) : ℝ :=
  Real.exp (-z / 2) *
    (Real.exp (-0.2067 * (L + Real.log 0.001) / z) -
      Real.exp (-0.478 * (L + Real.log 0.001) / z))

theorem original_endpoints {L : ℝ} (hL : 3100 ≤ L) :
    0 < Real.log (3.36 * L ^ (3 : ℕ)) ∧
      Real.log (3.36 * L ^ (3 : ℕ)) ≤ Real.log (10 * Real.pi * L ^ (7 : ℕ)) := by
  have hL1 : 1 ≤ L := by linarith
  have hp : 1 ≤ L ^ (3 : ℕ) := one_le_pow₀ hL1
  constructor
  · apply Real.log_pos
    linarith
  · apply Real.log_le_log (by positivity)
    have hp4 : 1 ≤ L ^ (4 : ℕ) := one_le_pow₀ hL1
    have hpi : 3.36 ≤ 10 * Real.pi := by linarith [Real.pi_gt_three]
    calc
      3.36 * L ^ (3 : ℕ) ≤ 10 * Real.pi * L ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right hpi (by positivity)
      _ ≤ 10 * Real.pi * L ^ (3 : ℕ) * L ^ (4 : ℕ) :=
        le_mul_of_one_le_right (by positivity) hp4
      _ = 10 * Real.pi * L ^ (7 : ℕ) := by ring

theorem originalKernel_nonneg {L z : ℝ} (hL : 3100 ≤ L) (hz : 0 < z) :
    0 ≤ originalKernel L z := by
  have hh := original_H_ge_scaling hL
  have hH : 0 ≤ L + Real.log (0.001 : ℝ) := by nlinarith [sq_nonneg (scaling L)]
  unfold originalKernel
  apply mul_nonneg (Real.exp_pos _).le
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hz.le
  nlinarith

theorem gaussian_phase {L z : ℝ} (hL : 3100 ≤ L)
    (hz : 0 < z) (hzu : z ≤ 60 * scaling L) :
    35.75 * scaling L + (z - 35.75 * scaling L) ^ 2 / (120 * scaling L) ≤
      z / 2 + 0.2067 * (L + Real.log 0.001) / z := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have hh := original_H_ge_scaling hL
  have hc : (35.75 * scaling L) ^ 2 / 2 ≤
      0.2067 * (L + Real.log 0.001) := by nlinarith [sq_nonneg (scaling L)]
  have hd := div_le_div_of_nonneg_left (sq_nonneg (z - 35.75 * scaling L))
    (by positivity : 0 < 2 * z) (by linarith : 2 * z ≤ 120 * scaling L)
  calc
    _ ≤ 35.75 * scaling L + (z - 35.75 * scaling L) ^ 2 / (2 * z) :=
      add_le_add_right hd _
    _ = z / 2 + ((35.75 * scaling L) ^ 2 / 2) / z := by field_simp; ring
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_right hc hz.le) _

theorem originalKernel_le_gaussian {L z : ℝ} (hL : 3100 ≤ L)
    (hz : 0 < z) (hzu : z ≤ 60 * scaling L) :
    originalKernel L z ≤ Real.exp (-35.75 * scaling L) *
      Real.exp (-(1 / (120 * scaling L)) * (z - 35.75 * scaling L) ^ 2) := by
  unfold originalKernel
  calc
    _ ≤ Real.exp (-z / 2) * Real.exp (-0.2067 * (L + Real.log 0.001) / z) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp (-z / 2 + -0.2067 * (L + Real.log 0.001) / z) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hp := gaussian_phase hL hz hzu
      calc
        _ = -(z / 2 + 0.2067 * (L + Real.log 0.001) / z) := by ring
        _ ≤ -(35.75 * scaling L + (z - 35.75 * scaling L) ^ 2 /
          (120 * scaling L)) := neg_le_neg hp
        _ = _ := by ring

theorem originalKernel_integrable {L : ℝ} (hL : 3100 ≤ L) :
    IntervalIntegrable (originalKernel L) volume
      (Real.log (3.36 * L ^ (3 : ℕ))) (Real.log (10 * Real.pi * L ^ (7 : ℕ))) := by
  have he := original_endpoints hL
  apply ContinuousOn.intervalIntegrable_of_Icc he.2
  unfold originalKernel
  have hn : ∀ z ∈ Set.Icc (Real.log (3.36 * L ^ (3 : ℕ)))
      (Real.log (10 * Real.pi * L ^ (7 : ℕ))), z ≠ 0 :=
    fun z hz => ne_of_gt (he.1.trans_le hz.1)
  have hc : ContinuousOn (fun z : ℝ => -z / 2)
      (Set.Icc (Real.log (3.36 * L ^ (3 : ℕ))) (Real.log (10 * Real.pi * L ^ (7 : ℕ)))) := by
    fun_prop
  exact (Real.continuous_exp.comp_continuousOn hc).mul
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.div continuousOn_id hn)).sub
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.div continuousOn_id hn)))

theorem original_integral_le_gaussian {L : ℝ} (hL : 3100 ≤ L) :
    (∫ z in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (10 * Real.pi * L ^ (7 : ℕ)),
      originalKernel L z) ≤ 20 * scaling L * Real.exp (-35.75 * scaling L) := by
  have hs := scaling_bounds hL
  have hr : 0 < scaling L := by linarith
  have he := original_endpoints hL
  let b := 1 / (120 * scaling L)
  have hb : 0 < b := by dsimp [b]; positivity
  have hg : Continuous (fun z : ℝ => Real.exp (-b * (z - 35.75 * scaling L) ^ 2)) := by
    fun_prop
  have hi := intervalIntegral.integral_mono_on he.2 (originalKernel_integrable hL)
    ((hg.const_mul (Real.exp (-35.75 * scaling L))).intervalIntegrable _ _) (fun z hz =>
      originalKernel_le_gaussian hL (he.1.trans_le hz.1)
        (hz.2.trans (original_upper_le_scaling hL)))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (f := fun z : ℝ => Real.exp (-b * z ^ 2))] at hi
  have hfull : (∫ z in (Real.log (3.36 * L ^ (3 : ℕ)) - 35.75 * scaling L)..
      (Real.log (10 * Real.pi * L ^ (7 : ℕ)) - 35.75 * scaling L),
      Real.exp (-b * z ^ 2)) ≤ Real.sqrt (Real.pi / b) := by
    rw [intervalIntegral.integral_of_le (sub_le_sub_right he.2 _), ← integral_gaussian]
    exact setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
      (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le))
  have hroot : Real.sqrt (Real.pi / b) ≤ 20 * scaling L := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    dsimp [b]
    simp only [div_eq_mul_inv, inv_inv, one_mul]
    have hpi : Real.pi ≤ 10 / 3 := by linarith [Real.pi_lt_d2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) hr.le,
      mul_le_mul_of_nonneg_right hpi hr.le]
  exact hi.trans ((mul_le_mul_of_nonneg_left (hfull.trans hroot)
    (Real.exp_pos _).le).trans_eq (by ring))

theorem fixed_exponential_certificate : Real.exp (-35.75 : ℝ) ≤ 0.00000000000000032 := by
  have hpos : 0 < Real.exp (35.75 : ℝ) := Real.exp_pos _
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ hpos).mpr
  have he : (2.718 : ℝ) ^ (35 : ℕ) * (1 + 0.75 + 0.75 ^ (2 : ℕ) / 2) ≤
      Real.exp (35.75 : ℝ) := by
    calc
      _ ≤ Real.exp 1 ^ (35 : ℕ) * Real.exp 0.75 :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num)
          (by linarith [Real.exp_one_gt_d9]) _)
          (by nlinarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.75)])
          (by norm_num) (by positivity)
      _ = Real.exp 35.75 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  linarith

theorem exponential_absorbs_scaling {r : ℝ} (hr : 1 ≤ r) :
    r ^ (5 : ℕ) * Real.exp (-35.75 * r) ≤ Real.exp (-35.75 : ℝ) := by
  have hr0 : 0 < r := by linarith
  have hh := Real.log_le_sub_one_of_pos hr0
  calc
    _ = Real.exp (5 * Real.log r + -35.75 * r) := by
      rw [Real.exp_add, show (5 : ℝ) = (5 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hr0]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem original_516_scalar_payment {L : ℝ} (hL : 3100 ≤ L) :
    112000 * L * sourceNu (L ^ (3 : ℕ)) *
      (∫ z in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (10 * Real.pi * L ^ (7 : ℕ)),
        Real.exp (-z / 2) *
          (Real.exp (-0.2067 * (L + Real.log 0.001) / z) -
            Real.exp (-0.478 * (L + Real.log 0.001) / z))) ≤ 0.000021 := by
  have hs := scaling_bounds hL
  have hn := sourceNu_le_scaling hL
  have hi := original_integral_le_gaussian hL
  change 112000 * L * sourceNu (L ^ (3 : ℕ)) *
    (∫ z in Real.log (3.36 * L ^ (3 : ℕ))..Real.log (10 * Real.pi * L ^ (7 : ℕ)),
      originalKernel L z) ≤ _
  calc
    _ ≤ (112000 * L * (8 * scaling L ^ 2)) *
        (20 * scaling L * Real.exp (-35.75 * scaling L)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hn.2 (by positivity)
      · exact hi
      · apply intervalIntegral.integral_nonneg (original_endpoints hL).2
        intro z hz
        exact originalKernel_nonneg hL ((original_endpoints hL).1.trans_le hz.1)
      · positivity
    _ = (112000 * 3100 * 8 * 20) *
        (scaling L ^ (5 : ℕ) * Real.exp (-35.75 * scaling L)) := by nth_rw 1 [hs.2]; ring
    _ ≤ (112000 * 3100 * 8 * 20) * Real.exp (-35.75 : ℝ) :=
      mul_le_mul_of_nonneg_left (exponential_absorbs_scaling hs.1) (by norm_num)
    _ ≤ (112000 * 3100 * 8 * 20) * 0.00000000000000032 :=
      mul_le_mul_of_nonneg_left fixed_exponential_certificate (by norm_num)
    _ ≤ 0.000021 := by norm_num

end LiuWang.Proof.SourceRoute.SecondArc.Continuation
