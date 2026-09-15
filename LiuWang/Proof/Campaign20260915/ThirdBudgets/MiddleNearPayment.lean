import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleNearScalar
import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleDensityPayment
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Count

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

theorem middle_theorem_two_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y alpha : ℝ} (hy : lowHeight ≤ y) (ha : sourceCutoff q 0.2067 y < alpha) :
    familyCount q alpha y ≤ 2 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hxy := M3_table_domain hN hq hy
  have hqy : (q : ℝ) ≤ (q : ℝ) * y := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (lowHeight_ge_one.trans hy) hq0.le
  have h := MultiZeroRepulsion.Continuation.general_theorem_two
    (show 8000000000 ≤ (q : ℝ) * y by linarith [hxy.1]) hqy
  have he : (q : ℝ) * y / q = y := by field_simp
  rw [he] at h
  have h : MultiZeroRepulsion.strictFamilyCount q (sourceCutoff q 0.2067 y) y ≤ 2 := by
    simpa only [sourceCutoff, show (2067 / 10000 : ℝ) = 0.2067 by norm_num] using h
  exact (Source525526.strict_to_closed_count ha).trans h

theorem middle_sparse_count_integral {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X y : ℝ} (hX : 1 ≤ X) (hy : lowHeight ≤ y) :
    countIntegral q X y (sourceCutoff q 0.2067 y) (sourceCutoff q 0.10367089 y) ≤
      2 * Real.exp (-0.10367089 * Real.log X / Real.log ((q : ℝ) * y)) := by
  have hX0 : 0 < X := by linarith
  have ho := sourceCutoff_order hN hq hy (d := 0.10367089) (e := 0.2067)
    (by norm_num) (by norm_num) (by norm_num)
  have hhalf : 1 / 2 ≤ sourceCutoff q 0.2067 y := by linarith [ho.1]
  calc
    _ ≤ ∫ alpha in (sourceCutoff q 0.2067 y)..(sourceCutoff q 0.10367089 y),
        2 * betaKernel X alpha := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ho.2.1
        (family_beta_integrable q y hX0 hhalf ho.2.1)
        (((betaKernel_continuous hX0).const_mul 2).intervalIntegrable _ _)
      intro alpha halpha
      have hc : (familyCount q alpha y : ℝ) ≤ 2 := by
        exact_mod_cast middle_theorem_two_count hN hq hy halpha.1
      have hk : 0 ≤ betaKernel X alpha :=
        mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.log_nonneg hX)
      nlinarith only [mul_le_mul_of_nonneg_left hc hk]
    _ = 2 * (X ^ (sourceCutoff q 0.10367089 y - 1) -
        X ^ (sourceCutoff q 0.2067 y - 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_betaKernel hX0]
    _ ≤ 2 * X ^ (sourceCutoff q 0.10367089 y - 1) := by
      nlinarith [Real.rpow_nonneg hX0.le (sourceCutoff q 0.2067 y - 1)]
    _ = _ := by rw [sourceCutoff, cutoff_power_exp hX0]

def middleNearCountEnvelope (L q y : ℝ) : ℝ :=
  14000 * Real.exp (-0.2067 * (L - 7) / Real.log (q * y)) +
    2 * Real.exp (-0.10367089 * (L - 7) / Real.log (q * y))

theorem middle_near_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {y : ℝ} (hy : lowHeight ≤ y) :
    countIntegral q (0.001 * N) y (sourceCutoff q 0.478 y) (sourceCutoff q 0.10367089 y) ≤
      middleNearCountEnvelope (sourceL N) q y := by
  have hX := original_middle_base_ge_one hN
  have ho := sourceCutoff_order hN hq hy (d := 0.2067) (e := 0.478)
    (by norm_num) (by norm_num) le_rfl
  have ho' := sourceCutoff_order hN hq hy (d := 0.10367089) (e := 0.2067)
    (by norm_num) (by norm_num) (by norm_num)
  have hs := countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX)
    (show 1 / 2 ≤ sourceCutoff q 0.478 y by linarith [ho.1]) ho.2.1 ho'.2.1
  rw [hs]
  have h1 := moving_14000_strip_bound hN hq hX hy (d := 0.2067) (by norm_num) (by norm_num)
  have h2 := middle_sparse_count_integral hN hq hX hy
  have hlog := LiuWang.Proof.SourceRoute.SecondArc.log_window_lower hN
  have hs0 : 0 ≤ Real.log ((q : ℝ) * y) := by
    linarith [M3_log_product_ge_thirty hN hq hy]
  have he (d : ℝ) (hd : 0 ≤ d) :
      Real.exp (-d * Real.log (0.001 * (N : ℝ)) / Real.log ((q : ℝ) * y)) ≤
        Real.exp (-d * (sourceL N - 7) / Real.log ((q : ℝ) * y)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hs0
    nlinarith [mul_le_mul_of_nonneg_left hlog hd]
  unfold middleNearCountEnvelope
  have h1' := mul_le_mul_of_nonneg_left (he 0.2067 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 14000)
  have h2' := mul_le_mul_of_nonneg_left (he 0.10367089 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [h1, h2, h1', h2']

theorem middle_log_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    34 ≤ Real.log ((q : ℝ) * lowHeight) := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlogL : 8 ≤ Real.log (sourceL N) :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hqlog := Real.log_le_log (pow_pos hL0 3) hq
  rw [Real.log_pow] at hqlog
  simp only [Nat.cast_ofNat] at hqlog
  have hlow : 10 ≤ Real.log lowHeight := by
    apply (Real.le_log_iff_exp_le lowHeight_pos).mpr
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.719) 10
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    unfold lowHeight
    linarith [Real.pi_gt_three]
  rw [Real.log_mul hq0.ne' lowHeight_pos.ne']
  linarith

theorem middle_near_log_substitution {q u v : ℝ}
    (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) (L : ℝ) :
    (∫ y in u..v, heightKernel (1 / 2) y * middleNearCountEnvelope L q y) =
      (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ) *
        ∫ t in Real.log (q * u)..Real.log (q * v), middleNearKernel L t := by
  rw [height_log_substitution hq hu hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have he : q * (Real.exp t / q) = Real.exp t := by field_simp
  unfold middleNearCountEnvelope middleNearKernel
  dsimp only
  rw [he, Real.log_exp]
  have hid (d : ℝ) : Real.exp (-t / 2 - d * (L - 7) / t) =
      Real.exp (-(1 / 2 : ℝ) * t) * Real.exp (-d * (L - 7) / t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid, hid]
  ring

theorem middle_near_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    (8 * N * Real.sqrt q / q.totient) *
      (∫ y in lowHeight..middleHeight N q, y ^ (-3 / 2 : ℝ) *
        countIntegral q (0.001 * N) y (sourceCutoff q 0.478 y) (sourceCutoff q 0.10367089 y)) ≤
      0.00006 * (N : ℝ) / sourceL N := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX := original_middle_base_ge_one hN
  have hc : ContinuousOn (middleNearCountEnvelope (sourceL N) q)
      (Set.uIcc lowHeight (middleHeight N q)) := by
    rw [Set.uIcc_of_le hh.1]
    intro y hy
    have hprod : (q : ℝ) * y ≠ 0 := (mul_pos hq0 (lowHeight_pos.trans_le hy.1)).ne'
    have hs : Real.log ((q : ℝ) * y) ≠ 0 := by
      linarith [M3_log_product_ge_thirty hN hq hy.1]
    unfold middleNearCountEnvelope
    fun_prop
  have hi := moving_strip_integrable hN hq hX le_rfl hh.1
    (d := 0.10367089) (e := 0.478) (p := 1 / 2) (by norm_num) (by norm_num) le_rfl
  have hF := heightKernel_mul_integrable lowHeight_pos hh.1 (1 / 2 : ℝ) hc.intervalIntegrable
  have hint := intervalIntegral.integral_mono_on hh.1 hi hF (fun y hy =>
    mul_le_mul_of_nonneg_left (middle_near_count_bound hN hq hy.1)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (Real.rpow_nonneg (lowHeight_pos.le.trans hy.1) _)))
  rw [middle_near_log_substitution hq0 lowHeight_pos (lowHeight_pos.trans_le hh.1)] at hint
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
      ((1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) * I) =
        (8 * N * ((q : ℝ) / q.totient)) * I := by
    calc
      _ = (8 * N / q.totient) * (Real.sqrt q * (q : ℝ) ^ (1 / 2 : ℝ)) * I := by ring
      _ = _ := by rw [hqq]; ring
  rw [hid] at hs
  simp only [heightKernel, show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    mul_assoc, intervalIntegral.integral_const_mul] at hs
  have hab : Real.log ((q : ℝ) * lowHeight) ≤ Real.log (10 * Real.pi * sourceL N ^ 7) := by
    rw [← he]
    exact Real.log_le_log (mul_pos hq0 lowHeight_pos) (mul_le_mul_of_nonneg_left hh.1 hq0.le)
  have hnon : 0 ≤ ∫ t in Real.log ((q : ℝ) * lowHeight)..
      Real.log (10 * Real.pi * sourceL N ^ 7), middleNearKernel (sourceL N) t :=
    intervalIntegral.integral_nonneg hab (fun t _ => by unfold middleNearKernel; positivity)
  have hprice := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (htotient.trans hnu) (show 0 ≤ 8 * (N : ℝ) by positivity)) hnon
  have hpaid := mul_le_mul_of_nonneg_left
    (middle_near_scalar_paid (sourceL_ge_3100 hN) (middle_log_lower hN hq) hab le_rfl)
    (Nat.cast_nonneg (α := ℝ) N)
  apply (le_div_iff₀ hL0).mpr
  have hbound := mul_le_mul_of_nonneg_right
    (show (8 * N * Real.sqrt q / q.totient) *
      (∫ y in lowHeight..middleHeight N q, y ^ (-3 / 2 : ℝ) *
        countIntegral q (0.001 * N) y (sourceCutoff q 0.478 y) (sourceCutoff q 0.10367089 y)) ≤
      (8 * N * sourceNu (sourceL N ^ 6)) *
        ∫ t in Real.log ((q : ℝ) * lowHeight)..Real.log (10 * Real.pi * sourceL N ^ 7),
          middleNearKernel (sourceL N) t by
        ring_nf at hs hprice ⊢
        linarith only [hs, hprice]) hL0.le
  nlinarith only [hbound, hpaid]

#print axioms middle_theorem_two_count
#print axioms middle_near_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
