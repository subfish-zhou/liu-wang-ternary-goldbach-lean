import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5ActualDomain

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem m5_integrated_density_envelope {L s z a : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hz : 0 ≤ z)
    (hzs : z ≤ (11 / 10) * s) (hgap : 4 * z ≤ L / 4) :
    (∫ alpha in a..(1 - 0.478 / s),
      L * Real.exp (L * (alpha - 1)) *
        (16541 * z ^ 6 + 24200 * z ^ 6 * Real.exp (4 * z * (1 - alpha)))) ≤
      600000 * s ^ 6 * Real.exp (-0.478 * L / s) := by
  have hk : 0 < L - 4 * z := by linarith
  have hfrac : L / (L - 4 * z) ≤ 4 / 3 := by
    apply (div_le_iff₀ hk).mpr
    linarith
  have h0 := integral_density_exponential (L := L) (D := 0)
    (a := a) (b := 1 - 0.478 / s) (by simpa using hL) hL.le
  simp only [zero_mul, Real.exp_zero, mul_one, sub_zero, div_self hL.ne'] at h0
  have hid0 : L * (1 - 0.478 / s - 1) = -0.478 * L / s := by ring
  rw [hid0] at h0
  have h1 := integral_density_exponential (L := L) (D := 4 * z)
    (a := a) (b := 1 - 0.478 / s) hk hL.le
  have he : (L - 4 * z) * (1 - 0.478 / s - 1) ≤ -0.478 * L / s + 2.104 := by
    apply (mul_le_mul_iff_left₀ hs).mp
    field_simp
    nlinarith
  have hexp : Real.exp ((L - 4 * z) * (1 - 0.478 / s - 1)) ≤
      9 * Real.exp (-0.478 * L / s) := by
    calc
      _ ≤ Real.exp (-0.478 * L / s + 2.104) := Real.exp_le_exp.mpr he
      _ = Real.exp (-0.478 * L / s) * Real.exp 2.104 := Real.exp_add _ _
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left exp_density_shift_le
          (Real.exp_pos (-0.478 * L / s)).le
  have h1 := h1.trans (mul_le_mul hfrac hexp (Real.exp_pos _).le (by norm_num))
  have hi0 : IntervalIntegrable (fun alpha => L * Real.exp (L * (alpha - 1)))
      volume a (1 - 0.478 / s) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun alpha => L * Real.exp (L * (alpha - 1)) *
      Real.exp (4 * z * (1 - alpha))) volume a (1 - 0.478 / s) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hid (alpha : ℝ) :
      L * Real.exp (L * (alpha - 1)) *
        (16541 * z ^ 6 + 24200 * z ^ 6 * Real.exp (4 * z * (1 - alpha))) =
      (16541 * z ^ 6) * (L * Real.exp (L * (alpha - 1))) +
        (24200 * z ^ 6) * (L * Real.exp (L * (alpha - 1)) *
          Real.exp (4 * z * (1 - alpha))) := by ring
  simp_rw [hid]
  rw [intervalIntegral.integral_add (hi0.const_mul _) (hi1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hp := add_le_add
    (mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ 16541 * z ^ 6))
    (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 24200 * z ^ 6))
  have hpow := pow_le_pow_left₀ hz hzs 6
  rw [mul_pow] at hpow
  have hpow := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-0.478 * L / s)).le
  have hnon : 0 ≤ s ^ 6 * Real.exp (-0.478 * L / s) := by positivity
  simp only [intervalIntegral.integral_const_mul] at hp ⊢
  nlinarith only [hp, hpow, hnon]

theorem m5_source_density_integral {q : ℕ} (hq : 0 < q) {X y s a : ℝ}
    (hX : 1 < X) (hy : 1 ≤ y) (hs : 0 < s)
    (hz : 36 ≤ Real.log ((q : ℝ) * y))
    (hzs : Real.log ((q : ℝ) * y) ≤ (11 / 10) * s)
    (hgap : 4 * Real.log ((q : ℝ) * y) ≤ Real.log X / 4)
    (hab : a ≤ 1 - 0.478 / s) :
    (∫ alpha in a..(1 - 0.478 / s), betaKernel X alpha * sourceDensity q y alpha) ≤
      600000 * s ^ 6 * Real.exp (-0.478 * Real.log X / s) := by
  have hX0 : 0 < X := by linarith
  have hL := Real.log_pos hX
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hy0 : 0 < y := by linarith
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have hly : Real.log y ≤ Real.log ((q : ℝ) * y) := by
    apply Real.log_le_log hy0
    nlinarith
  have hc : 17102 + 254231 / Real.log ((q : ℝ) * y) ≤ 24200 := by
    have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 254231)
      (by norm_num : (0 : ℝ) < 36) hz
    linarith
  have hid (alpha : ℝ) : betaKernel X alpha =
      Real.log X * Real.exp (Real.log X * (alpha - 1)) := by
    unfold betaKernel
    rw [Real.rpow_def_of_pos hX0]
    ring
  calc
    _ ≤ ∫ alpha in a..(1 - 0.478 / s),
        Real.log X * Real.exp (Real.log X * (alpha - 1)) *
          (16541 * Real.log ((q : ℝ) * y) ^ 6 +
            24200 * Real.log ((q : ℝ) * y) ^ 6 *
              Real.exp (4 * Real.log ((q : ℝ) * y) * (1 - alpha))) := by
      apply intervalIntegral.integral_mono_on hab
        (((betaKernel_continuous hX0).mul
          (sourceDensity_continuous hq hy0 (by linarith))).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _)
      intro alpha halpha
      have ha : alpha ≤ 1 := by
        have hd : 0 ≤ 0.478 / s := by positivity
        linarith [halpha.2]
      have hd := density_power_envelope hq hy (by linarith) ha
      have hp := pow_le_pow_left₀ hl hly 6
      have hh := add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16541))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc
            (pow_nonneg (show 0 ≤ Real.log ((q : ℝ) * y) by linarith) 6))
          (Real.exp_pos (4 * Real.log ((q : ℝ) * y) * (1 - alpha))).le)
      dsimp only [Pi.mul_apply]
      rw [hid]
      exact mul_le_mul_of_nonneg_left (hd.trans hh) (by positivity)
    _ ≤ _ := m5_integrated_density_envelope (Real.log_pos hX) hs (by linarith) hzs hgap

theorem m5_legal_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) {y : ℝ}
    (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N))
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (sourceCutoff q 0.478 (legalHeight q y)),
      (familyCount q alpha (legalHeight q y) : ℝ) ≤ sourceDensity q (legalHeight q y) alpha) :
    countIntegral q N (legalHeight q y) (59 / 60) (sourceCutoff q 0.478 y) ≤
      600000 * Real.log ((q : ℝ) * y) ^ 6 *
        Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) := by
  have hd := m5_legal_height_domain hN hq hq1 hy
  have hs := m5_log_domain hN hq1 hy
  have hX : (1 : ℝ) < N := by linarith [Real.add_one_le_exp (3100 : ℝ)]
  have hlow := (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1.trans hy.1
  have hcut := (sourceCutoff_order hN hq hlow (d := 0.478) (e := 0.478)
    (by norm_num) le_rfl le_rfl).1
  calc
    _ ≤ ∫ alpha in (59 / 60 : ℝ)..(sourceCutoff q 0.478 y),
        betaKernel N alpha * sourceDensity q (legalHeight q y) alpha := by
      apply intervalIntegral.integral_mono_on hcut
        (family_beta_integrable q _ (by linarith) (by norm_num) hcut)
        (((betaKernel_continuous (by linarith : (0 : ℝ) < N)).mul
          (sourceDensity_continuous (NeZero.pos q) (by linarith [hd.2.2.2.1])
            (by linarith [hd.2.2.2.2.1]))).intervalIntegrable _ _)
      intro alpha halpha
      exact mul_le_mul_of_nonneg_left
        (hdensity alpha ⟨halpha.1, halpha.2.trans (m5_cutoff_le_legal hN hq1 hy)⟩)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.log_nonneg hX.le))
    _ ≤ _ := m5_source_density_integral (NeZero.pos q) hX hd.2.2.2.1
      (by linarith [hs.2.1]) hd.2.2.2.2.1 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 hcut

theorem m5_count_bound_all_heights {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) {y : ℝ}
    (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N))
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (sourceCutoff q 0.478 (legalHeight q y)),
      (familyCount q alpha (legalHeight q y) : ℝ) ≤ sourceDensity q (legalHeight q y) alpha) :
    countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y) ≤
      (33643 + 254231 / Real.log ((q : ℝ) * y)) * Real.log ((q : ℝ) * y) ^ 6 *
        Real.exp ((4 * Real.log ((q : ℝ) * y) - Real.log q) / 60 -
          0.478 * sourceL N / Real.log ((q : ℝ) * y)) := by
  have hs := m5_log_domain hN hq1 hy
  have hlow := (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1.trans hy.1
  have hcut := (sourceCutoff_order hN hq hlow (d := 0.478) (e := 0.478)
    (by norm_num) le_rfl le_rfl).1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hc := (ThirdDomainTail.countIntegral_le_legal_height q hX (by norm_num) hcut).trans
    (m5_legal_count_bound hN hq hq1 hy hdensity)
  have he : (600000 : ℝ) ≤ 33643 * Real.exp 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 3
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith only [hp]
  have hexp : Real.exp 3 ≤
      Real.exp ((4 * Real.log ((q : ℝ) * y) - Real.log q) / 60) :=
    Real.exp_le_exp.mpr (by linarith [hs.2.2.2])
  have hcoef : (33643 : ℝ) ≤ 33643 + 254231 / Real.log ((q : ℝ) * y) := by
    have : 0 ≤ (254231 : ℝ) / Real.log ((q : ℝ) * y) :=
      div_nonneg (by norm_num) (by linarith [hs.2.1])
    linarith
  have hp := he.trans (mul_le_mul hcoef hexp (Real.exp_pos _).le
    (by linarith : (0 : ℝ) ≤ 33643 + 254231 / Real.log ((q : ℝ) * y)))
  have hm := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ Real.log ((q : ℝ) * y) ^ 6 *
      Real.exp (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) by positivity)
  apply hc.trans
  rw [show (4 * Real.log ((q : ℝ) * y) - Real.log q) / 60 -
      0.478 * sourceL N / Real.log ((q : ℝ) * y) =
    (4 * Real.log ((q : ℝ) * y) - Real.log q) / 60 +
      (-0.478 * sourceL N / Real.log ((q : ℝ) * y)) by ring, Real.exp_add]
  convert hm using 1 <;> ring

#print axioms m5_count_bound_all_heights

end LiuWang.Proof.Campaign20260915.ThirdBudgets
