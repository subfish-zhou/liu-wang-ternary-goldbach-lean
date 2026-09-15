import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowBetaScalar
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source524.LocalTaylor

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

def originalCountFactor (q : ℝ) : ℝ := 10006.8423 * Real.log q + 76180

def originalBaseScalar (L Q : ℝ) : ℝ :=
  L * Real.sqrt Q * lowCoefficient (1 / 2) * originalCountFactor Q * Real.exp (-L / 60)

theorem original_base_endpoint :
    (1.937 * (10006.8423 * 6 * 8.04 + 76180) * 3100 ^ 4 : ℝ) *
      Real.exp (-(3100 : ℝ) / 60) ≤ 0.00365 := by
  have h := Source524.exp_nat_add_lower 51 7 (u := 2 / 3) (by norm_num) (le_refl _)
  norm_num only [Nat.cast_ofNat, show (51 : ℝ) + 2 / 3 = 3100 / 60 by norm_num] at h
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h ⊢
  linarith only [h]

theorem original_base_global_decay {L : ℝ} (hL : 3100 ≤ L) :
    1.937 * L ^ 4 * (10006.8423 * (6 * Real.log L) + 76180) *
      Real.exp (-L / 60) ≤ 0.00365 := by
  have hpos : 0 < L := by linarith
  have hlog := WeightedLowZeros.Continuation.log_over_self_bound hL
  have hlog' : Real.log L ≤ 8.04 * (L / 3100) := by
    have h := (div_le_iff₀ hpos).mp hlog
    nlinarith
  have ha : 10006.8423 * (6 * Real.log L) + 76180 ≤
      (10006.8423 * 6 * 8.04 + 76180) * (L / 3100) := by nlinarith
  calc
    _ ≤ 1.937 * L ^ 4 * ((10006.8423 * 6 * 8.04 + 76180) * (L / 3100)) *
        Real.exp (-L / 60) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by positivity)) (Real.exp_pos _).le
    _ = (1.937 * (10006.8423 * 6 * 8.04 + 76180) / 3100) *
        (L ^ 5 * Real.exp (-L / 60)) := by ring
    _ ≤ (1.937 * (10006.8423 * 6 * 8.04 + 76180) / 3100) *
        (3100 ^ 5 * Real.exp (-(3100 : ℝ) / 60)) :=
      mul_le_mul_of_nonneg_left (fifth_power_decay hL) (by positivity)
    _ ≤ _ := by convert original_base_endpoint using 1; ring

theorem originalBaseScalar_paid {L Q : ℝ} (hL : 3100 ≤ L)
    (hQ : 1 ≤ Q) (hQ1 : Q ≤ L ^ 6) :
    originalBaseScalar L Q ≤ 0.00365 := by
  have hL0 : 0 < L := by linarith
  have hs : Real.sqrt Q ≤ L ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith only [hQ1]
  have hl := Real.log_le_log (by linarith : 0 < Q) hQ1
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog := Real.log_nonneg hQ
  have hb := mul_le_mul
    (mul_le_mul hs lowCoefficient_half_le (lowCoefficient_nonneg (by norm_num)) (by positivity))
    (show originalCountFactor Q ≤ 10006.8423 * (6 * Real.log L) + 76180 by
      unfold originalCountFactor; linarith)
    (show 0 ≤ originalCountFactor Q by unfold originalCountFactor; positivity) (by positivity)
  have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ L * Real.exp (-L / 60) by positivity)
  unfold originalBaseScalar
  nlinarith only [h, original_base_global_decay hL]

theorem original_base_scalar_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    (N : ℝ) * Real.sqrt q * lowCoefficient (1 / 2) *
      originalCountFactor q * (N : ℝ) ^ (-1 / 60 : ℝ) ≤
        0.00365 * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hLp : 0 < sourceL N := by linarith
  have h := originalBaseScalar_paid hL
    (by exact_mod_cast (NeZero.one_le : 1 ≤ q)) hq1
  have he : (N : ℝ) ^ (-1 / 60 : ℝ) = Real.exp (-sourceL N / 60) := by
    rw [Real.rpow_def_of_pos (natCast_pos_of_exp_le hN), sourceL]
    congr 1
    ring
  rw [he]
  apply (le_div_iff₀ hLp).mpr
  have h := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) N)
  unfold originalBaseScalar at h
  nlinarith only [h]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
