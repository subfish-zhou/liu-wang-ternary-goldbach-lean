import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.NuPower
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.SumIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation

def lowTailExponent : ℝ := 1 / 6 - 2 + 2 * 0.080521

theorem lowTailExponent_lt_neg_one : lowTailExponent < -1 := by
  norm_num [lowTailExponent]

theorem low_kernel_le_power {x : ℝ} (hx : 10000000000 ≤ x) :
    nuKernel (1 / 6) x ≤ x ^ lowTailExponent := by
  have hsq := pow_le_pow_left₀ (nu_pos (by linarith : 100000 ≤ x)).le
    (nu_le_source_power hx) 2
  have he : (x ^ (0.080521 : ℝ)) ^ 2 = x ^ (2 * 0.080521 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  rw [he] at hsq
  calc
    _ ≤ x ^ (1 / 6 - 2 : ℝ) * x ^ (2 * 0.080521 : ℝ) :=
      mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (by linarith) _)
    _ = _ := (Real.rpow_add (by linarith) _ _).symm

theorem low_power_integrable :
    IntegrableOn (fun x : ℝ => x ^ lowTailExponent) (Ioi 10000000000) :=
  integrableOn_Ioi_rpow_of_lt lowTailExponent_lt_neg_one (by norm_num)

theorem low_kernel_integrable :
    IntegrableOn (nuKernel (1 / 6)) (Ioi 10000000000) := by
  apply low_power_integrable.mono'
    (((nuKernel_continuousOn (1 / 6)).mono
      (show Ioi (10000000000 : ℝ) ⊆ Ici 100000 by
        intro x hx
        change 10000000000 < x at hx
        change 100000 ≤ x
        linarith)).aestronglyMeasurable
        measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 10000000000 < x at hx
  rw [Real.norm_eq_abs, abs_of_nonneg (nuKernel_nonneg (by linarith [hx]) _)]
  exact low_kernel_le_power hx.le

theorem low_power_integral :
    (∫ x : ℝ in Ioi 10000000000, x ^ lowTailExponent) =
      (10000000000 : ℝ) ^ (1 / 6 - 1 + 2 * 0.080521 : ℝ) /
        (5 / 6 - 2 * 0.080521) := by
  rw [integral_Ioi_rpow_of_lt lowTailExponent_lt_neg_one (by norm_num)]
  rw [show lowTailExponent + 1 = (1 / 6 - 1 + 2 * 0.080521 : ℝ) by
    unfold lowTailExponent; ring]
  rw [show (1 / 6 - 1 + 2 * 0.080521 : ℝ) = -(5 / 6 - 2 * 0.080521) by ring]
  exact neg_div_neg_eq _ _

theorem low_power_integral_le :
    (∫ x : ℝ in Ioi 10000000000, x ^ lowTailExponent) ≤ 0.000000282 := by
  rw [low_power_integral]
  have h := div_le_div_of_nonneg_right source_power_tail_endpoint
    (by norm_num : (0 : ℝ) ≤ 5 / 6 - 2 * 0.080521)
  exact h.trans (by norm_num)

theorem low_kernel_integral_le :
    (∫ x : ℝ in Ioi 10000000000, nuKernel (1 / 6) x) ≤ 0.000000282 := by
  apply (setIntegral_mono_on low_kernel_integrable low_power_integrable measurableSet_Ioi
    (fun _ hx => low_kernel_le_power hx.le)).trans low_power_integral_le

theorem low_finite_tail_le {P : ℝ} (hP : 10000000000 ≤ P) :
    (∫ x in (10000000000 : ℝ)..P, nuKernel (1 / 6) x) ≤ 0.000000282 := by
  rw [intervalIntegral.integral_of_le hP]
  apply (setIntegral_mono_set low_kernel_integrable _ (show Ioc (10000000000 : ℝ) P ⊆
    Ioi 10000000000 from fun _ hx => hx.1).eventuallyLE).trans low_kernel_integral_le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 10000000000 < x at hx
  exact nuKernel_nonneg (by linarith [hx]) _

theorem high_tail_primitive_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => 6 * t ^ (1 / 6 : ℝ)) (x ^ (-5 / 6 : ℝ)) x := by
  convert! (Real.hasDerivAt_rpow_const (p := (1 / 6 : ℝ)) (Or.inl hx.ne')).const_mul 6 using 1
  norm_num
  ring

theorem high_power_intervalIntegrable {P : ℝ} (hP : 10000000000 ≤ P) :
    IntervalIntegrable (fun x : ℝ => x ^ (-5 / 6 : ℝ)) volume 10000000000 P := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hP]
  exact continuousOn_id.rpow_const (fun x hx => Or.inl (by change x ≠ 0; linarith [hx.1]))

theorem high_power_integral {P : ℝ} (hP : 10000000000 ≤ P) :
    (∫ x in (10000000000 : ℝ)..P, x ^ (-5 / 6 : ℝ)) =
      6 * (P ^ (1 / 6 : ℝ) - (10000000000 : ℝ) ^ (1 / 6 : ℝ)) := by
  have hder : ∀ x ∈ uIcc (10000000000 : ℝ) P,
      HasDerivAt (fun t : ℝ => 6 * t ^ (1 / 6 : ℝ)) (x ^ (-5 / 6 : ℝ)) x := by
    rw [uIcc_of_le hP]
    intro x hx
    exact high_tail_primitive_hasDerivAt (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (high_power_intervalIntegrable hP)]
  ring

theorem ten_billion_sixth_root :
    (10000000000 : ℝ) ^ (1 / 6 : ℝ) = (10 : ℝ) ^ (5 / 3 : ℝ) := by
  rw [show (10000000000 : ℝ) = (10 : ℝ) ^ (10 : ℕ) by norm_num,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem high_finite_tail_le {P : ℝ} (hP : 10000000000 ≤ P) :
    (∫ x in (10000000000 : ℝ)..P, nuKernel (7 / 6) x) ≤
      nu P ^ 2 * 6 * (P ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) := by
  have h := intervalIntegral.integral_mono_on hP
    (nuKernel_intervalIntegrable (7 / 6) (by norm_num) hP)
    ((high_power_intervalIntegrable hP).const_mul (nu P ^ 2))
    (show ∀ x ∈ Icc (10000000000 : ℝ) P,
      nuKernel (7 / 6) x ≤ nu P ^ 2 * x ^ (-5 / 6 : ℝ) by
      intro x hx
      have hn := pow_le_pow_left₀ (nu_pos (by linarith [hx.1])).le
        (nu_monotoneOn (by change 100000 ≤ x; linarith [hx.1])
          (by change 100000 ≤ P; linarith) hx.2) 2
      simpa only [nuKernel, show (7 / 6 - 2 : ℝ) = -5 / 6 by norm_num, mul_comm] using
        mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (by linarith [hx.1]) (-5 / 6)))
  rw [intervalIntegral.integral_const_mul, high_power_integral hP, ten_billion_sixth_root] at h
  nlinarith [h]

theorem source419_tail {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ x in (10000000000 : ℝ)..sourceP N, nuKernel (1 / 6) x) ≤ 0.000000282 :=
  low_finite_tail_le (sourceP_ge_ten_billion hN)

theorem source422_tail {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ x in (10000000000 : ℝ)..sourceP N, nuKernel (7 / 6) x) ≤
      nu (sourceP N) ^ 2 * 6 *
        ((sourceP N) ^ (1 / 6 : ℝ) - (10 : ℝ) ^ (5 / 3 : ℝ)) :=
  high_finite_tail_le (sourceP_ge_ten_billion hN)

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
