import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.RealTail

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem real_countIntegral_tail_antitone {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {X u v d : ℝ} (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v)
    (hd : 0 ≤ d) (hd1 : d ≤ 0.478) :
    AntitoneOn (fun y => countIntegral q X 0 (sourceCutoff q d y) 1) (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  intro y hy z hz hyz
  have hlow := hu.trans hy.1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : 0 < Real.log ((q : ℝ) * y) := by
    linarith [M3_log_product_ge_thirty hN hq hlow]
  have hlog := Real.log_le_log (mul_pos hq0 (lowHeight_pos.trans_le hlow))
    (mul_le_mul_of_nonneg_left hyz hq0.le)
  have hcut : sourceCutoff q d y ≤ sourceCutoff q d z :=
    sub_le_sub_left (div_le_div_of_nonneg_left hd hl hlog) 1
  have hycut := sourceCutoff_order hN hq hlow hd le_rfl hd1
  have hzcut := sourceCutoff_order hN hq (hu.trans hz.1) hd le_rfl hd1
  have hs := countIntegral_split q 0 (lt_of_lt_of_le zero_lt_one hX)
    ((by norm_num : (1 / 2 : ℝ) ≤ 59 / 60).trans hycut.1) hcut hzcut.2.2
  have hn := countIntegral_nonneg q hX (y := 0) hcut
  linarith only [hs, hn]

theorem sourceHighRealTail_le_credit_without_local {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sourceHighRealTail N q ≤
      (5 * N * Real.sqrt q / q.totient) *
        ((middleHeight N q)⁻¹ * countIntegral q N 0 (59 / 60) 1) := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hu := lowHeight_pos.trans_le hh.1
  have hv := hu.trans_le hh.2
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hi := heightKernel_mul_integrable hu hh.2 (1 : ℝ)
    (real_countIntegral_tail_antitone hN hq hX hh.1 hh.2
      (d := 0.10367089) (by norm_num) (by norm_num)).intervalIntegrable
  have hic := (heightKernel_integrable hu hh.2 (1 : ℝ)).mul_const
    (countIntegral q N 0 (59 / 60) 1)
  have h :
      (∫ y in middleHeight N q..sourceT N, heightKernel 1 y *
        countIntegral q N 0 (sourceCutoff q 0.10367089 y) 1) ≤
      ∫ y in middleHeight N q..sourceT N,
        heightKernel 1 y * countIntegral q N 0 (59 / 60) 1 := by
    apply intervalIntegral.integral_mono_on hh.2 hi hic
    intro y hy
    have ho := sourceCutoff_order hN hq (hh.1.trans hy.1)
      (d := 0.10367089) (e := 0.10367089) (by norm_num) le_rfl (by norm_num)
    have hs := countIntegral_split q 0 (lt_of_lt_of_le zero_lt_one hX)
      (by norm_num : (1 / 2 : ℝ) ≤ 59 / 60) ho.1 ho.2.2
    have hn := countIntegral_nonneg q hX (y := 0) ho.1
    exact mul_le_mul_of_nonneg_left (by linarith only [hs, hn])
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Real.rpow_nonneg (hu.le.trans hy.1) _))
  rw [intervalIntegral.integral_mul_const, integral_heightKernel hu hh.2] at h
  have hn := countIntegral_nonneg q hX (y := 0) (by norm_num : (59 / 60 : ℝ) ≤ 1)
  have hc :
      ((middleHeight N q)⁻¹ - (sourceT N)⁻¹) * countIntegral q N 0 (59 / 60) 1 ≤
        (middleHeight N q)⁻¹ * countIntegral q N 0 (59 / 60) 1 := by
    nlinarith only [mul_nonneg (inv_nonneg.mpr hv.le) hn]
  simp only [heightKernel, one_mul, Real.rpow_neg_one,
    show -(1 : ℝ) - 1 = -2 by norm_num] at h
  exact mul_le_mul_of_nonneg_left (h.trans hc) (by positivity)

#print axioms real_countIntegral_tail_antitone
#print axioms sourceHighRealTail_le_credit_without_local

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
