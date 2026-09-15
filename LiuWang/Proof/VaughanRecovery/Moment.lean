import LiuWang.Proof.VaughanRecovery.Range

/-! 实际系数平方矩：+8 素数预算与已付高幂余项只支付一次。 -/

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.VaughanRecovery

open Interfaces Parameters ArithmeticBounds PrimeMoment LambdaMoment VaughanTypeII

def primeBudget (N : ℕ) (X : ℝ) : ℝ :=
  (Real.log X ^ 2 - Real.log (sourceVaughanU N) ^ 2) / 2 +
    8 * Real.log X + 2043 / 10000

theorem scalar_budget_291 {L u y x : ℝ}
    (hL : 3100 ≤ L)
    (hu : u = (2 * L - 4 * Real.log L) / 5)
    (hy : y = (3 * L - Real.log L) / 5)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    (x ^ 2 - u ^ 2) / 2 + 8 * x + 2043 / 10000 ≤ (291 / 1000) * y ^ 2 := by
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog := log_le_hundredth hL
  have hL0 : 0 ≤ L := by linarith
  have hu' : (49 / 125 : ℝ) * L ≤ u := by linarith
  have hy' : y ≤ (3 / 5 : ℝ) * L := by linarith
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hxsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have husq : ((49 / 125 : ℝ) * L) ^ 2 ≤ u ^ 2 :=
    pow_le_pow_left₀ (by positivity) hu' 2
  have hysq : y ^ 2 ≤ ((3 / 5 : ℝ) * L) ^ 2 :=
    pow_le_pow_left₀ hy0 hy' 2
  have hpay : 3100 * L ≤ L ^ 2 := by nlinarith
  nlinarith

theorem W1_add_high_le_primeBudget {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) :
    W1 N ((N : ℝ) / M) + 2043 / 10000 ≤ primeBudget N ((N : ℝ) / M) := by
  have hg := source_quotient_geometry hN hM hM'
  have hp := W1_le_8 (exp_2000_le_of_exp_3100_le hN) hg.2.1 hg.2.2.2.2
  unfold primeBudget
  linarith

theorem primeBudget_le_291 {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) :
    primeBudget N ((N : ℝ) / M) ≤
      (291 / 1000) * Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hg := source_quotient_geometry hN hM hM'
  exact scalar_budget_291 (sourceL_ge_3100 hN)
    (log_sourceVaughanU hn) (log_source_quotient_V hn)
    (Real.log_nonneg ((one_lt_sourceVaughanU hn).le.trans hg.2.1))
    (Real.log_le_log ((sourceVaughanU_pos hn).trans_le hg.2.1) hg.2.2.1)

theorem actual_moment_le_primeBudget {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) :
    (∑ m ∈ coefficientSupport N M, sourceLargeDivisorWeight N m ^ 2) ≤
      ((N : ℝ) / M) * primeBudget N ((N : ℝ) / M) :=
  (actualMoment_source_high_powers_sharp hN hM hM').trans
    (mul_le_mul_of_nonneg_left (W1_add_high_le_primeBudget hN hM hM')
      (div_nonneg (Nat.cast_nonneg N) (source_quotient_geometry hN hM hM').1.le))

theorem actual_moment_le_291 {N : ℕ} {M : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : ℝ) / sourceVaughanU N) :
    (∑ m ∈ coefficientSupport N M, sourceLargeDivisorWeight N m ^ 2) ≤
      (291 / 1000) * ((N : ℝ) / M) *
        Real.log ((N : ℝ) / sourceVaughanV N) ^ 2 := by
  apply (actual_moment_le_primeBudget hN hM hM').trans
  have hp := mul_le_mul_of_nonneg_left (primeBudget_le_291 hN hM hM')
    (div_nonneg (Nat.cast_nonneg N) (source_quotient_geometry hN hM hM').1.le)
  convert hp using 1
  ring

end LiuWang.Proof.VaughanRecovery
