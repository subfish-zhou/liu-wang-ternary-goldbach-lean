import LiuWang.Proof.VaughanTypeI.ClosedRows

/-!
# 实际带符号 S3 的约数重组与核界

由现有 Dirichlet 卷积的结合律重组 r、t，不丢失乘法重数。
系数界消费真正的 `vonMangoldt_sum`，不使用约数个数代替。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Finset Interfaces Parameters AnalyticNumberTheory.LargeSieve
open scoped ArithmeticFunction.zeta

private def cutoff (X : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ X then f n else 0, by simp⟩

def sourceSmallDivisorCoeff (N m : ℕ) : ℝ :=
  ∑ r ∈ m.divisors.filter (fun r : ℕ => (r : ℝ) ≤ sourceVaughanU N),
    if ((m / r : ℕ) : ℝ) ≤ sourceVaughanV N then
      ArithmeticFunction.vonMangoldt r * (ArithmeticFunction.moebius (m / r) : ℝ)
    else 0

private theorem sourceSmallDivisorCoeff_eq_mul (N m : ℕ) :
    sourceSmallDivisorCoeff N m =
      (cutoff (sourceVaughanU N) ArithmeticFunction.vonMangoldt *
        cutoff (sourceVaughanV N) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) m := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (f := fun r t => cutoff (sourceVaughanU N) ArithmeticFunction.vonMangoldt r *
      cutoff (sourceVaughanV N) (ArithmeticFunction.moebius : ArithmeticFunction ℝ) t)]
  simp only [sourceSmallDivisorCoeff, cutoff, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, sum_filter, ite_mul, zero_mul, mul_ite, mul_zero]
  apply sum_congr rfl
  intro r _
  split_ifs <;> rfl

theorem sourceLambda3_eq_neg_divisor_sum (N n : ℕ) :
    sourceLambda3 N n = -(∑ m ∈ n.divisors, sourceSmallDivisorCoeff N m) := by
  let f := cutoff (sourceVaughanU N) ArithmeticFunction.vonMangoldt
  let g := cutoff (sourceVaughanV N) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  have hsum : (∑ m ∈ n.divisors, sourceSmallDivisorCoeff N m) = (g * (f * ζ)) n := by
    simp_rw [sourceSmallDivisorCoeff_eq_mul]
    change (∑ m ∈ n.divisors, (f * g) m) = _
    rw [← ArithmeticFunction.coe_mul_zeta_apply, mul_comm f g, mul_assoc]
  rw [hsum, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun t r => g t * (f * ζ) r)]
  simp_rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [sourceLambda3, f, g, cutoff, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, sum_filter, ite_mul, zero_mul, mul_sum,
    mul_ite, mul_zero]
  congr 1
  apply sum_congr rfl
  intro t _
  by_cases ht : (t : ℝ) ≤ sourceVaughanV N <;> simp [ht]

theorem abs_sourceSmallDivisorCoeff_le_log (N m : ℕ) :
    |sourceSmallDivisorCoeff N m| ≤ Real.log m := by
  unfold sourceSmallDivisorCoeff
  calc
    _ ≤ ∑ r ∈ m.divisors.filter (fun r : ℕ => (r : ℝ) ≤ sourceVaughanU N),
        |if ((m / r : ℕ) : ℝ) ≤ sourceVaughanV N then
          ArithmeticFunction.vonMangoldt r * (ArithmeticFunction.moebius (m / r) : ℝ)
        else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ m.divisors, ArithmeticFunction.vonMangoldt r := by
      apply (sum_le_sum ?_).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ =>
          ArithmeticFunction.vonMangoldt_nonneg))
      intro r _
      split_ifs
      · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hμ : |(ArithmeticFunction.moebius (m / r) : ℝ)| ≤ 1 := by
          rcases ArithmeticFunction.moebius_eq_or (m / r) with h | h | h <;> simp [h]
        exact (mul_le_mul_of_nonneg_left hμ ArithmeticFunction.vonMangoldt_nonneg).trans_eq
          (mul_one _)
      · simp only [abs_zero]
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := ArithmeticFunction.vonMangoldt_sum

theorem sourceSmallDivisorCoeff_eq_zero {N m : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hm : sourceVaughanU N * sourceVaughanV N < (m : ℝ)) :
    sourceSmallDivisorCoeff N m = 0 := by
  unfold sourceSmallDivisorCoeff
  apply sum_eq_zero
  intro r hr
  apply if_neg
  intro ht
  have hrU := (mem_filter.mp hr).2
  have hdiv := (Nat.mem_divisors.mp (mem_filter.mp hr).1).1
  have hprod : (m : ℝ) = (r : ℝ) * (m / r : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
  have hle : (m : ℝ) ≤ sourceVaughanU N * sourceVaughanV N := by
    rw [hprod]
    exact mul_le_mul hrU ht (Nat.cast_nonneg _) (sourceVaughanU_pos hN).le
  exact (not_le.mpr hm) hle

theorem sourceS3_eq_closedRows {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    sourceS3 N α =
      -(∑ d ∈ Icc 1 ⌊sourceVaughanU N * sourceVaughanV N⌋₊,
        (sourceSmallDivisorCoeff N d : ℂ) *
          ∑ m ∈ closedRow N d, charReal ((m : ℝ) * ((d : ℝ) * α))) := by
  have hcut (n : ℕ) : (∑ d ∈ n.divisors, sourceSmallDivisorCoeff N d) =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ ⌊sourceVaughanU N * sourceVaughanV N⌋₊),
        sourceSmallDivisorCoeff N d := by
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hdnot
    apply sourceSmallDivisorCoeff_eq_zero hN
    have hnot : ¬ d ≤ ⌊sourceVaughanU N * sourceVaughanV N⌋₊ := by
      simpa only [mem_filter, hd, true_and] using hdnot
    exact (Nat.floor_lt (mul_pos (sourceVaughanU_pos hN) (sourceVaughanV_pos hN)).le).mp
      (Nat.lt_of_not_ge hnot)
  unfold sourceS3 windowSum
  simp_rw [sourceLambda3_eq_neg_divisor_sum, hcut]
  simp only [Complex.ofReal_neg, Complex.ofReal_sum, neg_mul, sum_neg_distrib, sum_mul]
  congr 1
  calc
    _ = ∑ n ∈ windowFinset N,
        ∑ d ∈ n.divisors.filter (fun d => d ≤ ⌊sourceVaughanU N * sourceVaughanV N⌋₊),
          (sourceSmallDivisorCoeff N d : ℂ) *
            charReal (((d * (n / d) : ℕ) : ℝ) * α) := by
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp (mem_filter.mp hd).1).1]
    _ = _ := by
      rw [sum_window_divisors_reindex N ⌊sourceVaughanU N * sourceVaughanV N⌋₊
        (fun d m => (sourceSmallDivisorCoeff N d : ℂ) * charReal (((d * m : ℕ) : ℝ) * α))]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro m _
      congr 2
      push_cast
      ring

theorem norm_sourceS3_le_kernel {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    ‖sourceS3 N α‖ ≤
      Real.log (sourceVaughanU N * sourceVaughanV N) *
        ∑ d ∈ Icc 1 ⌊sourceVaughanU N * sourceVaughanV N⌋₊,
          truncatedKernel ((N : ℝ) / d) ((d : ℝ) * α) := by
  rw [sourceS3_eq_closedRows hN, norm_neg, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro d hd
  have hd1 := (mem_Icc.mp hd).1
  have hdUV : (d : ℝ) ≤ sourceVaughanU N * sourceVaughanV N :=
    (Nat.le_floor_iff (mul_pos (sourceVaughanU_pos hN) (sourceVaughanV_pos hN)).le).mp
      (mem_Icc.mp hd).2
  have hcoeff := (abs_sourceSmallDivisorCoeff_le_log N d).trans
    (Real.log_le_log (by exact_mod_cast hd1) hdUV)
  have hlog : 0 ≤ Real.log (sourceVaughanU N * sourceVaughanV N) :=
    (abs_nonneg _).trans hcoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul hcoeff (norm_closedRow_charReal_le N hd1 α) (norm_nonneg _) hlog

end LiuWang.Proof.VaughanTypeI
