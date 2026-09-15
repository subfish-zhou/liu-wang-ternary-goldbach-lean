import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OrdinaryHeight
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.SourceWindows
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual ordinary zero counts integrated on the two original weighted height windows. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem ordinary_band_linear {q : ℕ} [NeZero q] {alpha u v p : ℝ}
    (ha : 0 ≤ alpha) (hu : lowHeight ≤ u) (huv : u ≤ v) (hp : 0 ≤ p) :
    densityBand q alpha u v p ≤
      ((q.totient : ℝ) / 3 * Real.log ((q : ℝ) * v)) *
        (v ^ (-p) * v + ∫ y in u..v, heightKernel p y * y) := by
  have hu0 := lowHeight_pos.trans_le hu
  have hv0 := hu0.trans_le huv
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hc (y : ℝ) (hy : y ∈ Set.Icc u v) :
      (familyCount q alpha y : ℝ) ≤
        ((q.totient : ℝ) / 3 * Real.log ((q : ℝ) * v)) * y := by
    have hy0 := hu0.trans_le hy.1
    have hl := Real.log_le_log (mul_pos hq0 (hu0.trans_le hy.1))
      (mul_le_mul_of_nonneg_left hy.2 hq0.le)
    have h := (ordinary_count_family q ha (hu.trans hy.1)).trans
      (mul_le_mul_of_nonneg_left hl (by positivity))
    ring_nf at h ⊢
    exact h
  have h := family_height_partialSummation q alpha hu0 huv hp
  have hi : (∫ y in u..v, heightKernel p y * familyCount q alpha y) ≤
      ((q.totient : ℝ) / 3 * Real.log ((q : ℝ) * v)) *
        ∫ y in u..v, heightKernel p y * y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on huv (family_height_integrable q alpha p hu0 huv)
      (((heightKernel_integrable hu0 huv p).mul_continuousOn continuous_id.continuousOn).const_mul _)
    intro y hy
    have hh : 0 ≤ heightKernel p y := by
      unfold heightKernel
      exact mul_nonneg hp (Real.rpow_nonneg (hu0.trans_le hy.1).le _)
    have ht := mul_le_mul_of_nonneg_left (hc y hy) hh
    dsimp only [id_eq]
    nlinarith only [ht]
  have hv := mul_le_mul_of_nonneg_left (hc v ⟨huv, le_rfl⟩) (Real.rpow_nonneg hv0.le (-p))
  nlinarith only [h, hi, hv]

theorem ordinary_half_band {q : ℕ} [NeZero q] {alpha u v : ℝ}
    (ha : 0 ≤ alpha) (hu : lowHeight ≤ u) (huv : u ≤ v) :
    densityBand q alpha u v (1 / 2) ≤
      (2 / 3) * q.totient * Real.log ((q : ℝ) * v) * Real.sqrt v := by
  have hu0 := lowHeight_pos.trans_le hu
  have hv0 := hu0.trans_le huv
  have hi : (∫ y in u..v, heightKernel (1 / 2) y * y) = Real.sqrt v - Real.sqrt u := by
    have he (y : ℝ) (hy : y ∈ Set.uIcc u v) :
        heightKernel (1 / 2) y * y = (1 / 2) * y ^ (-1 / 2 : ℝ) := by
      have hy0 : 0 < y := by rw [Set.uIcc_of_le huv] at hy; exact hu0.trans_le hy.1
      unfold heightKernel
      rw [mul_assoc, ← Real.rpow_add_one hy0.ne']
      congr 2
      norm_num
    rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
    norm_num only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    ring
  have hv : v ^ (-(1 / 2 : ℝ)) * v = Real.sqrt v := by
    rw [← Real.rpow_add_one hv0.ne']
    norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
    exact (Real.sqrt_eq_rpow v).symm
  have h := ordinary_band_linear (q := q) ha hu huv (p := 1 / 2) (by norm_num)
  rw [hi, hv] at h
  have hlog : 0 ≤ Real.log ((q : ℝ) * v) := by
    apply Real.log_nonneg
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
    have hv1 : 1 ≤ v := by linarith [(ordinary_height_logs (hu.trans huv)).1]
    nlinarith
  have hn : 0 ≤ (q.totient : ℝ) * Real.log ((q : ℝ) * v) * Real.sqrt u := by positivity
  nlinarith only [h, hn]

theorem ordinary_inverse_band {q : ℕ} [NeZero q] {alpha u v : ℝ}
    (ha : 0 ≤ alpha) (hu : lowHeight ≤ u) (huv : u ≤ v) :
    densityBand q alpha u v 1 ≤
      ((q.totient : ℝ) / 3) * Real.log ((q : ℝ) * v) * (1 + Real.log (v / u)) := by
  have hu0 := lowHeight_pos.trans_le hu
  have hv0 := hu0.trans_le huv
  have hi : (∫ y in u..v, heightKernel 1 y * y) = Real.log (v / u) := by
    have he (y : ℝ) (hy : y ∈ Set.uIcc u v) :
        heightKernel 1 y * y = y⁻¹ := by
      have hy0 : 0 < y := by rw [Set.uIcc_of_le huv] at hy; exact hu0.trans_le hy.1
      unfold heightKernel
      rw [one_mul, ← Real.rpow_add_one hy0.ne']
      norm_num
      exact Real.rpow_neg_one y
    rw [intervalIntegral.integral_congr he, integral_inv_of_pos hu0 hv0]
  have h := ordinary_band_linear (q := q) ha hu huv (p := 1) (by norm_num)
  rw [hi, Real.rpow_neg_one, inv_mul_cancel₀ hv0.ne'] at h
  simpa only [mul_assoc] using h

theorem original_middle_ordinary_band {N q : ℕ} [NeZero q] {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) (ha : 0 ≤ alpha) :
    (Real.sqrt q / q.totient) * densityBand q alpha lowHeight (middleHeight N q) (1 / 2) ≤
      5 * sourceL N ^ (3.5 : ℝ) * Real.log (10 * Real.pi * sourceL N ^ 7) := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have horder := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hv0 := lowHeight_pos.trans_le horder.1
  have hqv : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  have hpow : (sourceL N ^ (3.5 : ℝ)) ^ 2 = sourceL N ^ (7 : ℕ) := by
    rw [← Real.rpow_mul_natCast hL0.le]
    norm_num
  have hs : Real.sqrt q * Real.sqrt (middleHeight N q) ≤ (15 / 2) * sourceL N ^ (3.5 : ℝ) := by
    have hs1 := Real.sq_sqrt hq0.le
    have hs2 := Real.sq_sqrt hv0.le
    have hh : (Real.sqrt q * Real.sqrt (middleHeight N q)) ^ 2 = 10 * Real.pi * sourceL N ^ 7 := by
      rw [mul_pow, hs1, hs2, hqv]
    have hb := mul_le_mul_of_nonneg_right (show 10 * Real.pi ≤ (15 / 2 : ℝ) ^ 2 by linarith [Real.pi_lt_four])
      (pow_nonneg hL0.le 7)
    nlinarith [Real.sqrt_nonneg (q : ℝ), Real.sqrt_nonneg (middleHeight N q),
      Real.rpow_pos_of_pos hL0 (3.5 : ℝ)]
  have h := mul_le_mul_of_nonneg_left (ordinary_half_band (q := q) ha le_rfl horder.1)
    (show 0 ≤ Real.sqrt q / q.totient by positivity)
  rw [hqv] at h
  have hlog : 0 ≤ Real.log (10 * Real.pi * sourceL N ^ 7) := by
    rw [← hqv]
    apply Real.log_nonneg
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
    have hv1 : 1 ≤ middleHeight N q := by linarith [(ordinary_height_logs horder.1).1]
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hs hlog
  apply h.trans
  field_simp
  nlinarith only [hs]

theorem original_high_ordinary_band {N q : ℕ} [NeZero q] {alpha : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) (ha : 0 ≤ alpha) :
    densityBand q alpha (middleHeight N q) (sourceT N) 1 ≤
      101 * q.totient * Real.log (sourceL N) ^ 2 := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hl : 8 ≤ Real.log (sourceL N) :=
    WeightedLowZeros.Continuation.log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hT0 : 0 < sourceT N := pow_pos hL0 15
  have hV0 := lowHeight_pos.trans_le hh.1
  have hV : sourceL N ≤ middleHeight N q := by
    unfold middleHeight
    apply (le_div_iff₀ hq0).mpr
    have ht := mul_le_mul_of_nonneg_left hq1 hL0.le
    change sourceL N * (q : ℝ) ≤ sourceL N * sourceL N ^ 6 at ht
    have hp := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 10 * Real.pi by linarith [Real.pi_gt_three]) (pow_nonneg hL0.le 7)
    nlinarith only [ht, hp]
  have hlogq := Real.log_le_log hq0 hq1
  rw [sourceP1, Real.log_pow] at hlogq
  have hlogT : Real.log (sourceT N) = 15 * Real.log (sourceL N) := by
    rw [sourceT, Real.log_pow]
    norm_num
  have hlogV := Real.log_le_log hL0 hV
  have hz : Real.log ((q : ℝ) * sourceT N) ≤ 21 * Real.log (sourceL N) := by
    rw [Real.log_mul hq0.ne' hT0.ne', hlogT]
    norm_num at hlogq
    linarith
  have hr : 1 + Real.log (sourceT N / middleHeight N q) ≤
      (101 / 7) * Real.log (sourceL N) := by
    rw [Real.log_div hT0.ne' hV0.ne', hlogT]
    linarith
  have hr0 : 0 ≤ 1 + Real.log (sourceT N / middleHeight N q) := by
    have h := Real.log_nonneg ((one_le_div hV0).mpr hh.2)
    linarith
  have hp := mul_le_mul hz hr hr0 (by linarith : 0 ≤ 21 * Real.log (sourceL N))
  have hp := mul_le_mul_of_nonneg_left hp (show 0 ≤ (q.totient : ℝ) / 3 by positivity)
  have h := ordinary_inverse_band (q := q) ha hh.1 hh.2
  nlinarith only [h, hp]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
