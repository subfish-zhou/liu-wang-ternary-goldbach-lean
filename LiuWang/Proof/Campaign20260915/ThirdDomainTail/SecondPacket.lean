import LiuWang.Proof.Campaign20260915.ThirdDomainTail.SecondTail

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem second_c1_cutoff_ge_source_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
    59 / 60 ≤ siegelCutoff q y := by
  have hd := exact_scale_domain hN hq hy.1
  have hl : 10 ≤ Real.log ((q : ℝ) * y) := by
    apply (Real.le_log_iff_exp_le (by linarith [hd.2.1])).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 10
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith [hd.2.1]
  have hden : 60 ≤ 9.645908801 * Real.log ((q : ℝ) * y) := by linarith
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 60) hden
  unfold siegelCutoff
  linarith

theorem second_densityBand_sqrt (q : ℕ) [NeZero q] (alpha u v : ℝ) :
    SourceRoute.ThirdArc.densityBand q alpha u v (1 / 2) = bandMass q alpha u v := by
  simp only [SourceRoute.ThirdArc.densityBand, bandMass,
    Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv]

theorem second_alpha_height_reduction_c1 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    (∫ alpha in (59 / 60 : ℝ)..1, alphaKernel (0.001 * (N : ℝ)) alpha *
      bandMass q alpha (omegaCutoff N q) (middleUpper N q)) ≤
      (1 / Real.sqrt (middleUpper N q)) *
        countIntegral q (0.001 * (N : ℝ)) (middleUpper N q) (59 / 60)
          (siegelCutoff q (middleUpper N q)) +
        (1 / 2 : ℝ) * ∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
          countIntegral q (0.001 * (N : ℝ)) y (59 / 60) (siegelCutoff q y) := by
  have hh := middle_height_domain hN hq
  have hX := window_base_ge_one hN
  have hx : 0 < 0.001 * (N : ℝ) := lt_of_lt_of_le zero_lt_one hX
  have hcut (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :=
    second_c1_cutoff_ge_source_split hN hq hy
  have hc (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
      countIntegral q (0.001 * (N : ℝ)) y (59 / 60) 1 -
          countIntegral q (0.001 * (N : ℝ)) 0 (59 / 60) 1 ≤
        countIntegral q (0.001 * (N : ℝ)) y (59 / 60) (siegelCutoff q y) :=
    second_nonreal_countIntegral_le_truncated hX (by norm_num) (hcut y hy)
      (hh.1.le.trans hy.1) (by linarith [(middle_log_domain hN hq hy).2.1]) (hlocal y hy)
  have hi := moving_count_strip_integrable (q := q) hx hh.2.1
    (a := fun _ => (59 / 60 : ℝ)) (b := siegelCutoff q) continuousOn_const
    (siegelCutoff_continuous hN hq) (fun _ _ => by norm_num) hcut
  have hki := heightKernel_mul_integrable hh.1 hh.2.1 (1 / 2 : ℝ) hi
  have h := densityBand_integral_le_counts_sub_real q hX
    (a := 59 / 60) (b := 1) (p := 1 / 2) (by norm_num) (by norm_num) hh.1 hh.2.1
    (by norm_num)
  have hbound :
      (middleUpper N q) ^ (-(1 / 2) : ℝ) *
          (countIntegral q (0.001 * (N : ℝ)) (middleUpper N q) (59 / 60) 1 -
            countIntegral q (0.001 * (N : ℝ)) 0 (59 / 60) 1) +
        (∫ y in omegaCutoff N q..middleUpper N q,
          SourceRoute.ThirdArc.heightKernel (1 / 2) y *
            (countIntegral q (0.001 * (N : ℝ)) y (59 / 60) 1 -
              countIntegral q (0.001 * (N : ℝ)) 0 (59 / 60) 1)) ≤
      (middleUpper N q) ^ (-(1 / 2) : ℝ) *
        countIntegral q (0.001 * (N : ℝ)) (middleUpper N q) (59 / 60)
          (siegelCutoff q (middleUpper N q)) +
        ∫ y in omegaCutoff N q..middleUpper N q, SourceRoute.ThirdArc.heightKernel (1 / 2) y *
          countIntegral q (0.001 * (N : ℝ)) y (59 / 60) (siegelCutoff q y) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hc _ ⟨hh.2.1, le_rfl⟩)
        (Real.rpow_nonneg (hh.1.le.trans hh.2.1) _)
    · apply intervalIntegral.integral_mono_on hh.2.1
        (countIntegral_sub_real_height_integrable q hX (by norm_num) (by norm_num)
          hh.1 hh.2.1) hki
      intro y hy
      exact mul_le_mul_of_nonneg_left (hc y hy)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (Real.rpow_nonneg (hh.1.le.trans hy.1) _))
  have hcost := h.trans hbound
  simp only [second_densityBand_sqrt] at hcost
  simp only [SourceRoute.ThirdArc.heightKernel,
    show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    Real.rpow_neg (hh.1.le.trans hh.2.1), ← Real.sqrt_eq_rpow,
    mul_assoc, intervalIntegral.integral_const_mul] at hcost
  simpa only [one_div, SourceRoute.ThirdArc.betaKernel, alphaKernel, heightKernel] using hcost

theorem middlePacket_original_c1_count_reduction {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hlocal : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) *
            bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
          (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              bandMass q alpha (omegaCutoff N q) (middleUpper N q)) +
          (1 / Real.sqrt (middleUpper N q)) *
            countIntegral q (0.001 * (N : ℝ)) (middleUpper N q) (59 / 60)
              (siegelCutoff q (middleUpper N q)) +
          (1 / 2 : ℝ) * ∫ y in omegaCutoff N q..middleUpper N q, heightKernel y *
            countIntegral q (0.001 * (N : ℝ)) y (59 / 60) (siegelCutoff q y)) := by
  apply (source_53_packet hN ha eta).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith only [second_alpha_height_reduction_c1 hN hq hlocal]

#print axioms second_c1_cutoff_ge_source_split
#print axioms second_alpha_height_reduction_c1
#print axioms middlePacket_original_c1_count_reduction

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
