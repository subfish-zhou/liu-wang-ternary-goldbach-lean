import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer.Kernel
import LiuWang.Proof.GlobalZeroDensity.WeightedMean

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open LiuWang.Proof.GlobalZeroDensity
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

def kernelTail (u : ℝ) : ℝ := 1 / (2 + Real.exp u)

theorem kernelTail_pos (u : ℝ) : 0 < kernelTail u := by
  unfold kernelTail; positivity

theorem kernelTail_continuous : Continuous kernelTail := by
  unfold kernelTail
  exact continuous_const.div (continuous_const.add Real.continuous_exp) (fun _ => by positivity)

theorem kernelTail_derivative (u : ℝ) :
    HasDerivAt kernelTail (-sourceKernel u) u := by
  have h := (sourceKernel_primitive u).neg
  change HasDerivAt (fun x : ℝ => -(-(2 + Real.exp x)⁻¹)) (-sourceKernel u) u at h
  change HasDerivAt (fun x : ℝ => 1 / (2 + Real.exp x)) (-sourceKernel u) u
  simpa only [neg_neg, one_div] using h

theorem kernelTail_le_exp (u : ℝ) : kernelTail u ≤ Real.exp (-u) := by
  rw [kernelTail, Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos u) (by linarith)

theorem kernel_le_exp (u : ℝ) : sourceKernel u ≤ Real.exp (-u) := by
  rw [sourceKernel, Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (Real.exp_pos u)).mpr
  nlinarith [Real.exp_pos u]

theorem kernelTail_moment_integrable (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * kernelTail u) (Ioi 0) := by
  have hi := exp_moment_integrable (y := 1) (by norm_num) n
  simp only [div_one] at hi
  apply hi.mono' ((continuous_id.pow n).mul kernelTail_continuous).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖u ^ n * kernelTail u‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hu.le n) (kernelTail_pos u).le)]
  exact mul_le_mul_of_nonneg_left (kernelTail_le_exp u) (pow_nonneg hu.le n)

theorem kernel_moment_integrable (n : ℕ) :
    IntegrableOn (fun u : ℝ => sourceKernel u * u ^ n) (Ioi 0) := by
  have hi := exp_moment_integrable (y := 1) (by norm_num) n
  simp only [div_one] at hi
  apply hi.mono' (sourceKernel_continuous.mul (continuous_id.pow n)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖sourceKernel u * u ^ n‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (sourceKernel_pos u).le (pow_nonneg hu.le n)), mul_comm]
  exact mul_le_mul_of_nonneg_left (kernel_le_exp u) (pow_nonneg hu.le n)

theorem kernelTail_moment_limit (n : ℕ) :
    Tendsto (fun u : ℝ => u ^ n * kernelTail u) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg (pow_nonneg hu n) (kernelTail_pos u).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_le_mul_of_nonneg_left (kernelTail_le_exp u) (pow_nonneg hu n)

theorem kernel_moment_zero :
    (∫ u in Ioi (0 : ℝ), sourceKernel u) = 1 / 3 := by
  simpa using (show (∫ u in Ioi (0 : ℝ), sourceKernel u) = 1 / (2 + Real.exp 0) from
    sourceKernel_tail 0).trans (by norm_num)

theorem kernel_moment_succ (n : ℕ) :
    (∫ u in Ioi (0 : ℝ), sourceKernel u * u ^ (n + 1)) =
      (n + 1 : ℝ) * ∫ u in Ioi (0 : ℝ), u ^ n * kernelTail u := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => x ^ (n + 1) * kernelTail x)
      ((n + 1 : ℝ) * (u ^ n * kernelTail u) - sourceKernel u * u ^ (n + 1)) u := by
    convert! ((hasDerivAt_pow (n + 1) u).mul (kernelTail_derivative u)) using 1
    simp [Nat.cast_add, Nat.cast_one]
    ring
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (fun u _ => hd u)
    (((kernelTail_moment_integrable n).const_mul (n + 1 : ℝ)).sub
      (kernel_moment_integrable (n + 1))) (kernelTail_moment_limit (n + 1))
  rw [integral_sub ((kernelTail_moment_integrable n).const_mul (n + 1 : ℝ))
    (kernel_moment_integrable (n + 1)), integral_const_mul] at hi
  simp only [zero_pow (Nat.succ_ne_zero n), zero_mul, sub_zero] at hi
  linarith

theorem kernelTail_integral :
    (∫ u in Ioi (0 : ℝ), kernelTail u) = Real.log 3 / 2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun x : ℝ => -(Real.log (1 + 2 * Real.exp (-x))) / 2) (kernelTail u) u := by
    have he : HasDerivAt (fun x : ℝ => 1 + 2 * Real.exp (-x))
        (-2 * Real.exp (-u)) u := by
      convert! ((((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).const_mul 2).const_add 1) using 1
      simp
    convert! ((he.log (by positivity)).neg.div_const 2) using 1
    rw [kernelTail, Real.exp_neg]
    field_simp
    ring
  have hl : Tendsto (fun x : ℝ => -(Real.log (1 + 2 * Real.exp (-x))) / 2)
      atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have h := (((he.const_mul 2).const_add 1).log (by norm_num)).neg.div_const 2
    simpa using h
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun u _ => hd u)
    (by simpa using kernelTail_moment_integrable 0) hl
  norm_num at hi ⊢
  linarith

theorem kernel_moment_one :
    (∫ u in Ioi (0 : ℝ), sourceKernel u * u) = Real.log 3 / 2 := by
  simpa [kernelTail_integral] using kernel_moment_succ 0

theorem kernelTail_upper (u : ℝ) :
    kernelTail u ≤ Real.exp (-u) - (10 / 9) * Real.exp (-u / (1 / 2)) +
      (4 / 9) * Real.exp (-u / (1 / 3)) := by
  have hp := Real.exp_pos (-u)
  have hpow2 : Real.exp (-u / (1 / 2)) = Real.exp (-u) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  have hpow3 : Real.exp (-u / (1 / 3)) = Real.exp (-u) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  have he : kernelTail u = Real.exp (-u) / (1 + 2 * Real.exp (-u)) := by
    rw [kernelTail, Real.exp_neg]
    field_simp
    ring
  rw [he, hpow2, hpow3]
  apply (div_le_iff₀ (by positivity : 0 < 1 + 2 * Real.exp (-u))).mpr
  nlinarith [sq_nonneg (Real.exp (-u) * (1 - Real.exp (-u)))]

theorem kernel_moment_two :
    (∫ u in Ioi (0 : ℝ), sourceKernel u * u ^ 2) ≤ 125 / 81 := by
  have h0 := exp_moment_integrable (y := 1) (by norm_num) 1
  have h2 := exp_moment_integrable (y := 1 / 2) (by norm_num) 1
  have h3 := exp_moment_integrable (y := 1 / 3) (by norm_num) 1
  simp only [pow_one, div_one] at h0 h2 h3
  have hm := integral_mono_ae (kernelTail_moment_integrable 1)
    ((h0.fun_sub (h2.const_mul (10 / 9))).fun_add (h3.const_mul (4 / 9))) ?_
  · simp only [pow_one] at hm
    rw [integral_add (h0.fun_sub (h2.const_mul (10 / 9))) (h3.const_mul (4 / 9)),
      integral_sub h0 (h2.const_mul (10 / 9)), integral_const_mul, integral_const_mul] at hm
    have e0 := exp_moment_integral (y := 1) (by norm_num) 1
    have e2 := exp_moment_integral (y := 1 / 2) (by norm_num) 1
    have e3 := exp_moment_integral (y := 1 / 3) (by norm_num) 1
    norm_num at e0 e2 e3
    rw [e0, e2, e3] at hm
    have he := kernel_moment_succ 1
    norm_num at he
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have h := mul_le_mul_of_nonneg_left (kernelTail_upper u) hu.le
    simpa only [pow_one, mul_add, mul_sub, mul_left_comm] using h

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets
