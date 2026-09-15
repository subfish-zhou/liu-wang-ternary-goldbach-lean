import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.SourceWindows
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.M6Certificate.Constants
import LiuWang.Proof.SourceRoute.SecondArc.SourceDomain

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem exp_neg_ten_le : Real.exp (-10 : ℝ) ≤ 1 / 20000 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
    (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) ≤ Real.exp 1) 10
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  rw [Real.exp_neg]
  have he : (20000 : ℝ) ≤ Real.exp 10 := by linarith only [hp]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he

theorem threeRowPrice_le_fourteen {X z : ℝ} (hz : 0 < Real.log z)
    (hlog : 40 * Real.log z ≤ Real.log X) :
    threeRowPrice X z 0 ≤ 14 := by
  have he (c : ℝ) (hc : 0.33 ≤ c) :
      Real.exp (-c * Real.log X / Real.log z) ≤ 1 / 20000 := by
    apply (Real.exp_le_exp.mpr ?_).trans exp_neg_ten_le
    apply (div_le_iff₀ hz).mpr
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ c by linarith)
    have hn := mul_le_mul_of_nonneg_right hc hz.le
    nlinarith only [hm, hn, hz]
  have h36 := he 0.36 (by norm_num)
  have h33 := he 0.33 le_rfl
  have h48 := (Real.exp_pos (-0.478 * Real.log X / Real.log z)).le
  simp only [threeRowPrice, neg_zero, zero_mul, zero_div, Real.exp_zero]
  linarith only [h36, h33, h48]

theorem middle_endpoint_log_ratio {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    0 < Real.log ((q : ℝ) * middleHeight N q) ∧
      40 * Real.log ((q : ℝ) * middleHeight N q) ≤ Real.log (0.001 * (N : ℝ)) := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have he : (q : ℝ) * middleHeight N q = 10 * Real.pi * sourceL N ^ 7 := by
    unfold middleHeight
    field_simp
  rw [he]
  refine ⟨(M6Certificate.original_log_interval hL).1, ?_⟩
  rw [Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0)
    (pow_pos hL0 7).ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hl := (div_le_iff₀ hL0).mp
    (LiuWang.Proof.WeightedLowZeros.Continuation.log_over_self_bound hL)
  linarith [M6Certificate.log_ten_pi_bounds.2,
    LiuWang.Proof.SourceRoute.SecondArc.log_window_lower hN]

theorem middle_endpoint_threeRowPrice_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    threeRowPrice (0.001 * N) ((q : ℝ) * middleHeight N q) 0 ≤ 14 :=
  threeRowPrice_le_fourteen (middle_endpoint_log_ratio hN).1
    (middle_endpoint_log_ratio hN).2

theorem middle_endpoint_sqrt_lower {L : ℝ} (hL : 3100 ≤ L) :
    250 * L ^ 3 ≤ Real.sqrt (10 * Real.pi * L ^ 7) := by
  have hL0 : 0 ≤ L := by linarith
  apply Real.le_sqrt_of_sq_le
  have hc : (62500 : ℝ) ≤ 10 * Real.pi * L := by
    nlinarith [Real.pi_gt_three]
  have h := mul_le_mul_of_nonneg_right hc (pow_nonneg hL0 6)
  calc
    (250 * L ^ 3) ^ 2 = 62500 * L ^ 6 := by ring
    _ ≤ (10 * Real.pi * L) * L ^ 6 := h
    _ = 10 * Real.pi * L ^ 7 := by ring

theorem middle_endpoint_scale {L : ℝ} (hL : 3100 ≤ L) :
    16 * 14 * (9 * (L / 3100)) / Real.sqrt (10 * Real.pi * L ^ 7) ≤
      (0.000001 : ℝ) / L := by
  have hL0 : 0 < L := by linarith
  have hb : 0 < Real.sqrt (10 * Real.pi * L ^ 7) := by positivity
  apply (div_le_div_iff₀ hb hL0).mpr
  have h := mul_le_mul_of_nonneg_left (middle_endpoint_sqrt_lower hL)
    (by norm_num : (0 : ℝ) ≤ 0.000001)
  have hp := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 3100 by linarith)
  nlinarith only [h, hp, sq_nonneg L]

theorem middle_endpoint_coefficient {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q) =
      16 * N * ((q : ℝ) / q.totient) / Real.sqrt (10 * Real.pi * sourceL N ^ 7) := by
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos q))
  have hb : 0 < Real.sqrt (10 * Real.pi * sourceL N ^ 7) := by positivity
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [middleHeight, Real.sqrt_div (by positivity)]
  calc
    _ = 16 * N * (Real.sqrt q * Real.sqrt q) / q.totient /
        Real.sqrt (10 * Real.pi * sourceL N ^ 7) := by
      field_simp
    _ = _ := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg q)]
      ring

theorem middle_endpoint_table_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        threeRowPrice (0.001 * N) ((q : ℝ) * middleHeight N q) 0 ≤
      0.000001 * (N : ℝ) / sourceL N := by
  have hn := htotient.trans (hnu.trans
    (M6Certificate.sourceNu_sixth_bounds (sourceL_ge_3100 hN)).2)
  calc
    _ ≤ (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) * 14 :=
      mul_le_mul_of_nonneg_left (middle_endpoint_threeRowPrice_le hN) (by positivity)
    _ = (N : ℝ) *
        (16 * 14 * ((q : ℝ) / q.totient) /
          Real.sqrt (10 * Real.pi * sourceL N ^ 7)) := by
      rw [middle_endpoint_coefficient hN]
      ring
    _ ≤ (N : ℝ) *
        (16 * 14 * (9 * (sourceL N / 3100)) /
          Real.sqrt (10 * Real.pi * sourceL N ^ 7)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn (by norm_num)) (Real.sqrt_nonneg _))
        (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) * (0.000001 / sourceL N) :=
      mul_le_mul_of_nonneg_left (middle_endpoint_scale (sourceL_ge_3100 hN))
        (Nat.cast_nonneg N)
    _ = _ := by ring

theorem middle_endpoint_density_remainder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : sourceP N ≤ (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 ≤
      (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60)
          (1 - 0.478 / Real.log ((q : ℝ) * middleHeight N q)) +
        0.000001 * (N : ℝ) / sourceL N := by
  exact (original_middle_endpoint_table_bill hN hq hq1).trans
    (add_le_add le_rfl (middle_endpoint_table_paid hN htotient hnu))

#print axioms middle_endpoint_table_paid
#print axioms middle_endpoint_density_remainder

end LiuWang.Proof.Campaign20260915.ThirdBudgets
