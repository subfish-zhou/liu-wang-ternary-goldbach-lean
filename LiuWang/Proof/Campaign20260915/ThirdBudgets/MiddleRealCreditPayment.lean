import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleNearPayment
import LiuWang.Proof.Campaign20260915.ThirdBudgets.EndpointActualPayment
import LiuWang.Proof.Campaign20260915.ThirdDomainTail.NonrealFubini

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem middle_count_after_real_credit {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y)
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    countIntegral q X y (59 / 60) 1 - countIntegral q X 0 (59 / 60) 1 ≤
      countIntegral q X y (59 / 60) (sourceCutoff q 0.478 y) +
        countIntegral q X y (sourceCutoff q 0.478 y) (sourceCutoff q 0.10367089 y) := by
  have ho := sourceCutoff_order hN hq hy (d := 0.10367089) (e := 0.478)
    (by norm_num) (by norm_num) le_rfl
  have hX0 : 0 < X := by linarith
  have hh : 1 / 2 ≤ (59 / 60 : ℝ) := by norm_num
  have hreal := local_tail_integral_eq_real (X := X) (lowHeight_pos.le.trans hy)
    (show 0 < Real.log ((q : ℝ) * y) by linarith [M3_log_product_ge_thirty hN hq hy]) hlocal
  rw [countIntegral_split q y hX0 hh (ho.1.trans ho.2.1) ho.2.2,
    countIntegral_split q y hX0 hh ho.1 ho.2.1,
    countIntegral_split q 0 hX0 hh (ho.1.trans ho.2.1) ho.2.2, hreal]
  have hnon := countIntegral_nonneg q hX (y := 0) (ho.1.trans ho.2.1)
  linarith only [hnon]

theorem middle_integral_after_real_credit {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hlocal : ∀ y ∈ Set.Icc lowHeight (middleHeight N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    (∫ y in lowHeight..middleHeight N q, heightKernel (1 / 2) y *
      (countIntegral q (0.001 * N) y (59 / 60) 1 - countIntegral q (0.001 * N) 0 (59 / 60) 1)) ≤
      (∫ y in lowHeight..middleHeight N q, heightKernel (1 / 2) y *
        countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y)) +
      ∫ y in lowHeight..middleHeight N q, heightKernel (1 / 2) y *
        countIntegral q (0.001 * N) y (sourceCutoff q 0.478 y) (sourceCutoff q 0.10367089 y) := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hX := original_middle_base_ge_one hN
  have hnon := ThirdDomainTail.countIntegral_sub_real_height_integrable q hX
    (a := 59 / 60) (b := 1) (p := 1 / 2) (by norm_num) (by norm_num) lowHeight_pos hh.1
  have hd := heightKernel_mul_integrable lowHeight_pos hh.1 (1 / 2 : ℝ)
    (moving_countIntegral_monotone hN hq hX le_rfl hh.1 (d := 0.478)
      (by norm_num) le_rfl).intervalIntegrable
  have hn := moving_strip_integrable hN hq hX le_rfl hh.1
    (d := 0.10367089) (e := 0.478) (p := 1 / 2) (by norm_num) (by norm_num) le_rfl
  rw [← intervalIntegral.integral_add hd hn]
  apply intervalIntegral.integral_mono_on hh.1 hnon (hd.add hn)
  intro y hy
  have h := mul_le_mul_of_nonneg_left (middle_count_after_real_credit hN hq hX hy.1 (hlocal y hy))
    (show 0 ≤ heightKernel (1 / 2) y from
      mul_nonneg (by norm_num) (Real.rpow_nonneg (lowHeight_pos.le.trans hy.1) _))
  simpa only [mul_add] using h

theorem sigma5_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6))
    (hlocal : ∀ y ∈ Set.Icc lowHeight (middleHeight N q),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    sigma5 N q ≤ 0.1337 * (N : ℝ) / sourceL N := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hX := original_middle_base_ge_one hN
  have hlow := sigma5_low_beta_paid hN hq1
  have habel := ThirdDomainTail.densityBand_integral_le_counts_sub_real q hX
    (a := 59 / 60) (b := 1) (p := 1 / 2) (by norm_num) (by norm_num)
    lowHeight_pos hh.1 (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left habel
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient by positivity)
  have hdom := m5_legal_height_domain hN hq hq1 ⟨le_rfl, hh.2⟩
  have hend := middle_endpoint_original_paid hN hq hq1
    (hdensity _ ⟨hdom.2.1, hdom.2.2.1⟩) htotient hnu
  have hd := middle_density_original_paid hN hq hq1 hdensity htotient hnu
  have hn := middle_near_original_paid hN hq hq1 htotient hnu
  have hi := mul_le_mul_of_nonneg_left (middle_integral_after_real_credit hN hq hq1 hlocal)
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient by positivity)
  have hreal := countIntegral_nonneg q hX (y := 0) (by norm_num : (59 / 60 : ℝ) ≤ 1)
  have hu : (middleHeight N q) ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt (middleHeight N q) := by
    rw [Real.rpow_neg (lowHeight_pos.le.trans hh.1), ← Real.sqrt_eq_rpow, one_div]
  rw [hu] at hscaled
  have hrealScaled := mul_nonneg
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q) by positivity) hreal
  have hNL : 0 ≤ (N : ℝ) / sourceL N :=
    div_nonneg (Nat.cast_nonneg N) (sourceL_pos (exp_2000_le_of_exp_3100_le hN)).le
  simp only [heightKernel, show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    mul_assoc, intervalIntegral.integral_const_mul] at hscaled hi
  ring_nf at hlow hscaled hend hd hn hi hrealScaled hNL ⊢
  linarith only [hlow, hscaled, hend, hd, hn, hi, hrealScaled, hNL]

#print sigma5_original_paid
#print axioms middle_count_after_real_credit
#print axioms sigma5_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
