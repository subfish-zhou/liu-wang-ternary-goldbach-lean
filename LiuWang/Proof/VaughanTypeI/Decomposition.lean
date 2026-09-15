import AnalyticNumberTheory.Sieve.VaughanIdentity
import LiuWang.Proof.ArithmeticBounds.ContinuationConsumer

/-!
# 原窗口上的实际 Vaughan 四项

复用已证的卷积恒等式；实截点始终是冻结的 U、V，自然截点仅取其下整。
第四项直接使用现有 `sourceLargeDivisorWeight`，但不使用左开端点的
`sourceVaughanInnerSupport`。本叶不导入第一类估计。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.VaughanTypeI

open Finset Interfaces Parameters ArithmeticBounds
open AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
open scoped ArithmeticFunction

def sourceLambda1 (N n : ℕ) : ℝ :=
  if (n : ℝ) ≤ sourceVaughanU N then ArithmeticFunction.vonMangoldt n else 0

def sourceLambda2 (N n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ sourceVaughanV N),
    (ArithmeticFunction.moebius t : ℝ) * Real.log (n / t : ℕ)

def sourceLambda3 (N n : ℕ) : ℝ :=
  -(∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ sourceVaughanV N),
    ∑ r ∈ (n / t).divisors.filter (fun r : ℕ => (r : ℝ) ≤ sourceVaughanU N),
      (ArithmeticFunction.moebius t : ℝ) * ArithmeticFunction.vonMangoldt r)

def sourceLambda4 (N n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => sourceVaughanV N < (t : ℝ)),
    (ArithmeticFunction.moebius t : ℝ) * sourceLargeDivisorWeight N (n / t)

def windowSum (N : ℕ) (α : ℝ) (w : ℕ → ℝ) : ℂ :=
  ∑ n ∈ windowFinset N, (w n : ℂ) * charReal ((n : ℝ) * α)

def sourceS1 (N : ℕ) (α : ℝ) : ℂ := windowSum N α (sourceLambda1 N)
def sourceS2 (N : ℕ) (α : ℝ) : ℂ := windowSum N α (sourceLambda2 N)
def sourceS3 (N : ℕ) (α : ℝ) : ℂ := windowSum N α (sourceLambda3 N)
def sourceS4 (N : ℕ) (α : ℝ) : ℂ := windowSum N α (sourceLambda4 N)

theorem vaughanIdentity_fourTerm (n u v : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      (if n ≤ u then ArithmeticFunction.vonMangoldt n else 0) +
        vaughanFirst n v - vaughanMiddle n v u + vaughanThird n v u := by
  have hsplit : vaughanMiddle n v u + vaughanSecond n v u =
      if n ≤ u then ArithmeticFunction.vonMangoldt n else 0 := by
    unfold vaughanMiddle vaughanSecond
    rw [← vaughanFullSecondSum n u]
    simpa only [not_le] using
      Finset.sum_filter_add_sum_filter_not (s := n.divisors)
        (p := fun t => t ≤ v)
        (f := fun t => ∑ r ∈ (n / t).divisors.filter (fun r => r ≤ u),
          (ArithmeticFunction.moebius t : ℝ) * ArithmeticFunction.vonMangoldt r)
  have hid := vaughanIdentity n v u
  linarith

theorem sourceLambda1_eq_floor {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (n : ℕ) :
    sourceLambda1 N n =
      if n ≤ ⌊sourceVaughanU N⌋₊ then ArithmeticFunction.vonMangoldt n else 0 := by
  simp only [sourceLambda1, Nat.le_floor_iff (sourceVaughanU_pos hN).le]

theorem sourceLambda2_eq_first {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (n : ℕ) :
    sourceLambda2 N n = vaughanFirst n ⌊sourceVaughanV N⌋₊ := by
  simp only [sourceLambda2, vaughanFirst,
    Nat.le_floor_iff (sourceVaughanV_pos hN).le]

theorem sourceLambda3_eq_neg_middle {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (n : ℕ) :
    sourceLambda3 N n =
      -vaughanMiddle n ⌊sourceVaughanV N⌋₊ ⌊sourceVaughanU N⌋₊ := by
  simp only [sourceLambda3, vaughanMiddle,
    Nat.le_floor_iff (sourceVaughanV_pos hN).le,
    Nat.le_floor_iff (sourceVaughanU_pos hN).le]

theorem sourceLambda4_eq_third {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (n : ℕ) :
    sourceLambda4 N n =
      vaughanThird n ⌊sourceVaughanV N⌋₊ ⌊sourceVaughanU N⌋₊ := by
  simp only [sourceLambda4, sourceLargeDivisorWeight, vaughanThird,
    Nat.floor_lt (sourceVaughanV_pos hN).le,
    Nat.floor_lt (sourceVaughanU_pos hN).le, Finset.mul_sum]

theorem sourceLambda_decomposition {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      sourceLambda1 N n + sourceLambda2 N n + sourceLambda3 N n + sourceLambda4 N n := by
  rw [sourceLambda1_eq_floor hN, sourceLambda2_eq_first hN,
    sourceLambda3_eq_neg_middle hN, sourceLambda4_eq_third hN]
  simpa only [sub_eq_add_neg] using
    vaughanIdentity_fourTerm n ⌊sourceVaughanU N⌋₊ ⌊sourceVaughanV N⌋₊

theorem sourceS_decomposition {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (α : ℝ) :
    S N α = sourceS1 N α + sourceS2 N α + sourceS3 N α + sourceS4 N α := by
  change (∑ n ∈ windowFinset N,
      (ArithmeticFunction.vonMangoldt n : ℂ) * charReal ((n : ℝ) * α)) = _
  unfold sourceS1 sourceS2 sourceS3 sourceS4 windowSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [sourceLambda_decomposition hN n]
  push_cast
  ring

end LiuWang.Proof.VaughanTypeI
