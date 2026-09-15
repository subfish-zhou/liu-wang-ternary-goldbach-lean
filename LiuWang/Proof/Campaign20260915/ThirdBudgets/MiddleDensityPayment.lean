import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5ActualCount
import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleDensityScalar
import LiuWang.Proof.Campaign20260915.ThirdBudgets.EndpointTable

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem middle_legal_log_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) {y : ℝ}
    (hy : y ∈ Set.Icc lowHeight (middleHeight N q)) :
    1 ≤ legalHeight q y ∧
      36 ≤ Real.log ((q : ℝ) * legalHeight q y) ∧
      Real.log ((q : ℝ) * legalHeight q y) ≤ (11 / 10) * Real.log ((q : ℝ) * y) ∧
      4 * Real.log ((q : ℝ) * legalHeight q y) ≤ Real.log (0.001 * (N : ℝ)) / 10 ∧
      legalHeight q y ∈ Set.Icc
        (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy0 := lowHeight_pos.trans_le hy.1
  have hyle : y ≤ legalHeight q y := le_max_left _ _
  have hg := enlarged_height_source_domain hN hq hq1
  have hH : max (100000 / (q : ℝ)) (10000 * Real.log q) = 10000 * Real.log q :=
    le_antisymm hg.2 (le_max_right _ _)
  have hl := M3_density_logs hN hq hq1
  have hlow := M3_log_product_ge_thirty hN hq hy.1
  have hz : 36 ≤ Real.log ((q : ℝ) * legalHeight q y) := by
    apply hl.2.1.trans
    apply Real.log_le_log (mul_pos hq0 (lowHeight_pos.trans_le hg.1))
    apply mul_le_mul_of_nonneg_left _ hq0.le
    exact (le_max_right _ _).trans (le_max_right y _)
  have hratio : Real.log ((q : ℝ) * legalHeight q y) ≤
      (11 / 10) * Real.log ((q : ℝ) * y) := by
    unfold legalHeight
    rw [hH]
    by_cases h : 10000 * Real.log (q : ℝ) ≤ y
    · rw [max_eq_left h]
      linarith
    · rw [max_eq_right (le_of_not_ge h)]
      have hs := Real.log_le_log (mul_pos hq0 lowHeight_pos)
        (mul_le_mul_of_nonneg_left hy.1 hq0.le)
      exact hl.2.2.1.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have htop : legalHeight q y ≤ sourceT N :=
    max_le (hy.2.trans hh.2) (high_endpoint_source_domain hN hq1)
  refine ⟨lowHeight_ge_one.trans (hy.1.trans hyle), hz, hratio, ?_,
    le_max_right _ _, htop⟩
  have hU := m5_legal_height_domain hN hq hq1 ⟨le_rfl, hh.2⟩
  have hlog := Real.log_le_log (mul_pos hq0 (hy0.trans_le hyle))
    (mul_le_mul_of_nonneg_left
      (show legalHeight q y ≤ legalHeight q (middleHeight N q) from max_le_max_right _ hy.2) hq0.le)
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  have hs := hU.2.2.2.2.2.1
  rw [he, Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0)
    (pow_pos hL0 7).ne', Real.log_pow] at hs
  simp only [Nat.cast_ofNat] at hs
  have hlogL := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  linarith [M6Certificate.log_ten_pi_bounds.2,
    LiuWang.Proof.SourceRoute.SecondArc.log_window_lower hN]

theorem middle_density_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) {y : ℝ}
    (hy : y ∈ Set.Icc lowHeight (middleHeight N q))
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 (legalHeight q y)),
      (familyCount q alpha (legalHeight q y) : ℝ) ≤ sourceDensity q (legalHeight q y) alpha) :
    countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y) ≤
      500000 * Real.log ((q : ℝ) * y) ^ 6 *
        Real.exp (-0.478 * (sourceL N - 7) / Real.log ((q : ℝ) * y)) := by
  let s := Real.log ((q : ℝ) * y)
  let z := Real.log ((q : ℝ) * legalHeight q y)
  have hd := middle_legal_log_domain hN hq hq1 hy
  have hs0 : 0 < s := by linarith [M3_log_product_ge_thirty hN hq hy.1]
  have hX : (1 : ℝ) < 0.001 * N := by linarith [Real.add_one_le_exp (3100 : ℝ)]
  have hcut := (sourceCutoff_order hN hq hy.1 (d := 0.478) (e := 0.478)
    (by norm_num) le_rfl le_rfl).1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlog := Real.log_le_log (mul_pos hq0 (lowHeight_pos.trans_le hy.1))
    (mul_le_mul_of_nonneg_left (show y ≤ legalHeight q y from le_max_left _ _) hq0.le)
  have hcuts : sourceCutoff q 0.478 y ≤ sourceCutoff q 0.478 (legalHeight q y) :=
    sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num) hs0 hlog) 1
  have hc :
      countIntegral q (0.001 * N) (legalHeight q y) (59 / 60) (sourceCutoff q 0.478 y) ≤
        (10 / 9) * (16541 + 9 * 24200) * z ^ 6 *
          Real.exp (-0.478 * Real.log (0.001 * N) / s) := by
    calc
      _ ≤ ∫ alpha in (59 / 60 : ℝ)..(sourceCutoff q 0.478 y),
          betaKernel (0.001 * N) alpha * sourceDensity q (legalHeight q y) alpha := by
        apply intervalIntegral.integral_mono_on hcut
          (family_beta_integrable q _ (by linarith) (by norm_num) hcut)
          (((betaKernel_continuous (by linarith : (0 : ℝ) < 0.001 * N)).mul
            (sourceDensity_continuous (NeZero.pos q) (by linarith [hd.1])
              (by linarith [hd.2.1]))).intervalIntegrable _ _)
        intro alpha halpha
        exact mul_le_mul_of_nonneg_left
          (hdensity alpha ⟨halpha.1, halpha.2.trans hcuts⟩)
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg hX.le))
      _ ≤ _ := source_density_integral_bound (NeZero.pos q) hX hd.1 hs0
        hd.2.1 hd.2.2.1 hd.2.2.2.1 hcut
  have hcount := (ThirdDomainTail.countIntegral_le_legal_height q hX.le (by norm_num) hcut).trans hc
  have hpow := pow_le_pow_left₀ (by linarith [hd.2.1] : 0 ≤ z) hd.2.2.1 6
  rw [mul_pow] at hpow
  have hcoeff : (10 / 9 : ℝ) * (16541 + 9 * 24200) * z ^ 6 ≤ 500000 * s ^ 6 := by
    nlinarith only [hpow, pow_nonneg hs0.le 6]
  have hexp : Real.exp (-0.478 * Real.log (0.001 * N) / s) ≤
      Real.exp (-0.478 * (sourceL N - 7) / s) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (by linarith [LiuWang.Proof.SourceRoute.SecondArc.log_window_lower hN]) hs0.le
  exact hcount.trans (mul_le_mul hcoeff hexp (Real.exp_pos _).le (by positivity))

theorem middle_density_log_substitution {q u v : ℝ}
    (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) (L : ℝ) :
    (∫ y in u..v, heightKernel (1 / 2) y *
      (Real.log (q * y) ^ 6 * Real.exp (-0.478 * (L - 7) / Real.log (q * y)))) =
      (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ) *
        ∫ t in Real.log (q * u)..Real.log (q * v), middleDensityKernel L t := by
  rw [height_log_substitution hq hu hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have he : q * (Real.exp t / q) = Real.exp t := by field_simp
  dsimp only
  rw [he, Real.log_exp]
  unfold middleDensityKernel
  rw [show -t / 2 - 0.478 * (L - 7) / t =
      -(1 / 2 : ℝ) * t + (-0.478 * (L - 7) / t) by ring, Real.exp_add]
  ring

theorem middle_density_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ r ∈ Set.Icc (max (100000 / (q : ℝ)) (10000 * Real.log q)) (sourceT N),
      ∀ alpha ∈ Set.Icc (59 / 60 : ℝ) (sourceCutoff q 0.478 r),
        (familyCount q alpha r : ℝ) ≤ sourceDensity q r alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    (8 * N * Real.sqrt q / q.totient) *
      (∫ y in lowHeight..middleHeight N q, y ^ (-3 / 2 : ℝ) *
        countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y)) ≤
      (0.07227 + 0.03775) * (N : ℝ) / sourceL N := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX := original_middle_base_ge_one hN
  let F := fun y : ℝ => Real.log ((q : ℝ) * y) ^ 6 *
    Real.exp (-0.478 * (sourceL N - 7) / Real.log ((q : ℝ) * y))
  have hc : ContinuousOn F (Set.uIcc lowHeight (middleHeight N q)) := by
    rw [Set.uIcc_of_le hh.1]
    intro y hy
    have hy0 := lowHeight_pos.trans_le hy.1
    have hprod : (q : ℝ) * y ≠ 0 := (mul_pos hq0 hy0).ne'
    have hs : Real.log ((q : ℝ) * y) ≠ 0 := by
      linarith [M3_log_product_ge_thirty hN hq hy.1]
    dsimp only [F]
    fun_prop
  have hi := heightKernel_mul_integrable lowHeight_pos hh.1 (1 / 2 : ℝ)
    (moving_countIntegral_monotone hN hq hX le_rfl hh.1
      (d := 0.478) (by norm_num) le_rfl).intervalIntegrable
  have hiF := heightKernel_mul_integrable lowHeight_pos hh.1 (1 / 2 : ℝ) hc.intervalIntegrable
  have hint :
      (∫ y in lowHeight..middleHeight N q, heightKernel (1 / 2) y *
        countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y)) ≤
      500000 * ∫ y in lowHeight..middleHeight N q, heightKernel (1 / 2) y * F y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hh.1 hi (hiF.const_mul _)
    intro y hy
    have hd := middle_legal_log_domain hN hq hq1 hy
    have h := mul_le_mul_of_nonneg_left
      (middle_density_count_bound hN hq hq1 hy (hdensity _ hd.2.2.2.2))
      (show 0 ≤ heightKernel (1 / 2) y from
        mul_nonneg (by norm_num) (Real.rpow_nonneg (lowHeight_pos.le.trans hy.1) _))
    dsimp only [F]
    nlinarith only [h]
  dsimp only [F] at hint
  rw [middle_density_log_substitution hq0 lowHeight_pos (lowHeight_pos.trans_le hh.1)] at hint
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  rw [he] at hint
  have hs := mul_le_mul_of_nonneg_left hint
    (show 0 ≤ 16 * N * Real.sqrt q / q.totient by positivity)
  have hqq : Real.sqrt q * (q : ℝ) ^ (1 / 2 : ℝ) = q := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.mul_self_sqrt (Nat.cast_nonneg q)
  have hid (I : ℝ) : (16 * N * Real.sqrt q / q.totient) *
      (500000 * ((1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) * I)) =
        (8 * N * ((q : ℝ) / q.totient) * 500000) * I := by
    calc
      _ = (8 * N / q.totient * 500000) * (Real.sqrt q * (q : ℝ) ^ (1 / 2 : ℝ)) * I := by ring
      _ = _ := by rw [hqq]; ring
  rw [hid] at hs
  simp only [heightKernel, show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    mul_assoc, intervalIntegral.integral_const_mul] at hs
  have hab : Real.log ((q : ℝ) * lowHeight) ≤ Real.log (10 * Real.pi * sourceL N ^ 7) := by
    rw [← he]
    exact Real.log_le_log (mul_pos hq0 lowHeight_pos) (mul_le_mul_of_nonneg_left hh.1 hq0.le)
  have ha : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have hnon : 0 ≤ ∫ t in Real.log ((q : ℝ) * lowHeight)..
      Real.log (10 * Real.pi * sourceL N ^ 7), middleDensityKernel (sourceL N) t :=
    intervalIntegral.integral_nonneg hab (fun t _ => by unfold middleDensityKernel; positivity)
  have hprice := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (htotient.trans hnu) (show 0 ≤ 8 * (N : ℝ) by positivity))
      (by norm_num : (0 : ℝ) ≤ 500000)) hnon
  have hpaid := mul_le_mul_of_nonneg_left
    (middle_density_scalar_paid (sourceL_ge_3100 hN) ha hab le_rfl) (Nat.cast_nonneg (α := ℝ) N)
  change (N : ℝ) * (8 * sourceL N * sourceNu (sourceL N ^ 6) * 500000 *
    (∫ t in Real.log ((q : ℝ) * lowHeight)..Real.log (10 * Real.pi * sourceL N ^ 7),
      middleDensityKernel (sourceL N) t)) ≤ _ at hpaid
  apply (le_div_iff₀ hL0).mpr
  have hbound := mul_le_mul_of_nonneg_right
    (show (8 * N * Real.sqrt q / q.totient) *
      (∫ y in lowHeight..middleHeight N q, y ^ (-3 / 2 : ℝ) *
        countIntegral q (0.001 * N) y (59 / 60) (sourceCutoff q 0.478 y)) ≤
      (8 * N * sourceNu (sourceL N ^ 6) * 500000) *
        ∫ t in Real.log ((q : ℝ) * lowHeight)..Real.log (10 * Real.pi * sourceL N ^ 7),
          middleDensityKernel (sourceL N) t by
        ring_nf at hs hprice ⊢
        linarith only [hs, hprice]) hL0.le
  nlinarith only [hbound, hpaid]

#print middle_density_original_paid
#print axioms middle_density_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
