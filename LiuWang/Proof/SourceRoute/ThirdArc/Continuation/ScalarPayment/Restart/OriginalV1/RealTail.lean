import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Reduction
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OrdinaryPayment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

theorem source_reciprocal_rounding :
    (0.10367089 : ℝ) ≤ 1 / 9.645908801 := by norm_num

theorem source_local_region_parameters {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y : ℝ} (hy : lowHeight ≤ y) :
    10 ≤ (q : ℝ) * y ∧ 1 ≤ q ∧ (q : ℝ) ≤ (q : ℝ) * y ∧
      (q : ℝ) * y / q = y := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  refine ⟨by linarith [(M3_table_domain hN hq hy).1], NeZero.one_le, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (lowHeight_ge_one.trans hy) hq0.le
    simpa only [mul_one] using this
  · field_simp

theorem bandValues_nonreal {q : ℕ} [NeZero q] {chi : Character q}
    {alpha u v : ℝ} (hu : 0 < u) {rho : ℂ}
    (hrho : rho ∈ bandValues chi alpha u v) : rho.im ≠ 0 := by
  have hh := (mem_bandValues.mp hrho).2.2.2
  intro hz
  rw [hz, abs_zero] at hh
  linarith

theorem familyCount_above_local_cutoff_eq_real {q : ℕ} [NeZero q]
    {y alpha : ℝ} (hy : 0 ≤ y) (hlog : 0 < Real.log ((q : ℝ) * y))
    (halpha : sourceCutoff q 0.10367089 y < alpha)
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    familyCount q alpha y = familyCount q alpha 0 := by
  have hcut : 1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) ≤
      sourceCutoff q 0.10367089 y := by
    have h := div_le_div_of_nonneg_right source_reciprocal_rounding hlog.le
    dsimp only [sourceCutoff]
    rw [div_div] at h
    linarith
  have he (chi : Character q) : zeroValues chi alpha y = zeroValues chi alpha 0 := by
    ext rho
    simp only [mem_zeroValues]
    constructor
    · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
      have hr := hlocal chi rho hz h0 h1 hh ((hcut.trans_lt halpha).trans_le ha)
      exact ⟨hz, ⟨h0, h1, by simp [hr]⟩, ha⟩
    · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
      exact ⟨hz, ⟨h0, h1, hh.trans hy⟩, ha⟩
  simp only [familyCount, count, he]

theorem local_tail_integral_eq_real {q : ℕ} [NeZero q] {X y : ℝ}
    (hy : 0 ≤ y) (hlog : 0 < Real.log ((q : ℝ) * y))
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    countIntegral q X y (sourceCutoff q 0.10367089 y) 1 =
      countIntegral q X 0 (sourceCutoff q 0.10367089 y) 1 := by
  have hcut : sourceCutoff q 0.10367089 y ≤ 1 :=
    sub_le_self _ (div_nonneg (by norm_num) hlog.le)
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ (fun alpha halpha => by
    rw [Set.uIoc_of_le hcut] at halpha
    rw [familyCount_above_local_cutoff_eq_real hy hlog halpha.1 hlocal])

def sourceM5 (N q : ℕ) [NeZero q] : ℝ :=
  (5 * N * Real.sqrt q / q.totient) *
    ∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
      countIntegral q N y (59 / 60) (sourceCutoff q 0.478 y)

def sourceHighRealTail (N q : ℕ) [NeZero q] : ℝ :=
  (5 * N * Real.sqrt q / q.totient) *
    ∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
      countIntegral q N 0 (sourceCutoff q 0.10367089 y) 1

theorem equation_5_42_with_real_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hlocal : ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    (5 * N * Real.sqrt q / q.totient) *
      (∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
        countIntegral q N y (59 / 60) 1) =
      sourceM5 N q + sourceM6 N q + sourceHighRealTail N q := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hs := moving_countIntegral_split hN hq hX hh.1 hh.2
    (d := 0.10367089) (p := 1) (by norm_num) (by norm_num)
  simp only [heightKernel, one_mul, show -(1 : ℝ) - 1 = -2 by norm_num] at hs
  have ht : (∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
      countIntegral q N y (sourceCutoff q 0.10367089 y) 1) =
      ∫ y in middleHeight N q..sourceT N, y ^ (-2 : ℝ) *
        countIntegral q N 0 (sourceCutoff q 0.10367089 y) 1 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hh.2] at hy
    have hlow := hh.1.trans hy.1
    have hl : 0 < Real.log ((q : ℝ) * y) := by
      linarith [M3_log_product_ge_thirty hN hq hlow]
    dsimp only
    rw [local_tail_integral_eq_real (lowHeight_pos.trans_le hlow).le hl (hlocal y hy)]
  rw [hs, ht]
  unfold sourceM5 sourceM6 sourceHighRealTail
  ring

theorem sigma6_original_reduction_with_real_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hhigh : (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6))
    (hlocal : ∀ y ∈ Set.Icc (middleHeight N q) (sourceT N),
      ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    sigma6 N q ≤ (0.00012 + 7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
      sourceM5 N q + (N : ℝ) / sourceL N * m6OriginalScalar (sourceL N) +
        sourceHighRealTail N q := by
  have h := sigma6_low_and_endpoint_paid hN hq hq1 hhigh
  rw [equation_5_42_with_real_tail hN hq hq1 hlocal] at h
  linarith [equation_5_44_original_integral hN hq hq1 htotient hnu]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
