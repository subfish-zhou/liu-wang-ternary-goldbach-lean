import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.EndBounds

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

theorem expKernel_factor (A s : ℝ) :
    expKernel A s = (3100 : ℝ) ^ 4 * Real.exp (-s) * Real.exp (-A / s) := by
  unfold expKernel phase
  rw [show -s - A / s = -s + (-A / s) by ring, Real.exp_add]
  ring

theorem integrand35_kernels (s : ℝ) :
    integrand profile35 3100 s =
      2 * expKernel firstA s + 11 * expKernel (0.3221 * 3100) s +
        7 * expKernel (0.33 * 3100) s - 20 * expKernel 1116 s := by
  simp only [expKernel_factor]
  unfold integrand profile35
  have he : -(3100 : ℝ) / (c1 * s) = -(firstA : ℝ) / s := by
    norm_num [c1, firstA]
    ring
  rw [he]
  norm_num
  ring

theorem integrand36_kernels (s : ℝ) :
    integrand profile36 3100 s =
      2 * expKernel secondA s + 6 * expKernel (0.2743 * 3100) s +
        expKernel (0.28 * 3100) s + expKernel (0.3 * 3100) s +
        expKernel (0.31 * 3100) s + 2 * expKernel (0.32 * 3100) s +
        7 * expKernel (0.33 * 3100) s - 20 * expKernel 1116 s := by
  simp only [expKernel_factor]
  unfold integrand profile36
  norm_num [secondA]
  ring

theorem integrand35_signed_upper {s : ℝ} (hs : 0 < s) :
    integrand profile35 3100 s ≤ 2 * expKernel firstA s +
      18 * ((3100 : ℝ) ^ 4 * Real.exp (-58)) - 20 * expKernel 1116 s := by
  rw [integrand35_kernels]
  have h1 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.3221) hs
  have h2 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.33) hs
  linarith

theorem integrand36_signed_upper {s : ℝ} (hs : 0 < s) :
    integrand profile36 3100 s ≤ 2 * expKernel secondA s +
      18 * ((3100 : ℝ) ^ 4 * Real.exp (-58)) - 20 * expKernel 1116 s := by
  rw [integrand36_kernels]
  have h1 := remaining_kernel (le_refl (0.2743 : ℝ)) hs
  have h2 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.28) hs
  have h3 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.3) hs
  have h4 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.31) hs
  have h5 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.32) hs
  have h6 := remaining_kernel (by norm_num : (0.2743 : ℝ) ≤ 0.33) hs
  linarith

theorem signed_core_upper {f : ℝ → ℝ → ℝ} (hf : ∀ L, ContinuousOn (f L) (Set.Ioi 0))
    (hpos : ∀ L s, 0 < L → 0 < s → 0 ≤ f L s) (A : ℝ)
    (hpoint : ∀ s : ℝ, 0 < s → integrand f 3100 s ≤
      2 * expKernel A s + 18 * ((3100 : ℝ) ^ 4 * Real.exp (-58)) - 20 * expKernel 1116 s) :
    (∫ s in lower 3100..(60 : ℝ), integrand f 3100 s) ≤
      2 * (∫ s in (start : ℝ)..(60 : ℝ), expKernel A s) +
        1 / 100000000 - 20 * ((3100 : ℝ) ^ 4 / 3 ^ 69) := by
  have ha : (0 : ℝ) < start := by norm_num [start]
  have hab : (start : ℝ) ≤ 60 := by norm_num [start]
  have he := intervalIntegral.integral_mono_interval start_le_lower
    (height_bounds (L := 3100) le_rfl).2.1 le_rfl
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs =>
      mul_nonneg (by positivity : (0 : ℝ) ≤ 3100 ^ 4 * Real.exp (-s))
        (hpos _ _ (by norm_num) (ha.trans hs.1))))
    (integrand_integrable hf 3100 ha hab)
  have hi1 := (expKernel_integrable A ha hab).const_mul 2
  have hi2 : IntervalIntegrable (fun _ : ℝ => 18 * ((3100 : ℝ) ^ 4 * Real.exp (-58)))
      volume (start : ℝ) 60 := intervalIntegrable_const
  have hi3 := (expKernel_integrable 1116 ha hab).const_mul 20
  have hh := intervalIntegral.integral_mono_on hab (integrand_integrable hf 3100 ha hab)
    ((hi1.add hi2).sub hi3) (fun s hs => hpoint s (ha.trans_le hs.1))
  rw [intervalIntegral.integral_sub (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2] at hh
  have hr := remaining_fee
  simp only [intervalIntegral.integral_const_mul] at hh hr
  change (∫ s in lower 3100..(60 : ℝ), integrand f 3100 s) ≤
    ∫ s in (start : ℝ)..(60 : ℝ), integrand f 3100 s at he
  linarith [signed_negative_tail]

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536
