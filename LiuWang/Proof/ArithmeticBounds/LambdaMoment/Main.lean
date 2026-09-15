import LiuWang.Proof.ArithmeticBounds.LambdaMoment.Expansion

/-!
# 大 N 域上的实际 Vaughan 大约数 Λ 平方矩

证明 (6.13) 的有序重数分解，并实际代入 (6.14)、(6.15) 的高幂常数。
`W1` 仍为有限素数和；没有支付其 0.105 预算，也没有闭合整体平方矩或指数和。
这里只覆盖原应用的 `N ≥ exp 3100`，不声称覆盖 `N ≥ exp 30.95`。
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

open scoped BigOperators
open Parameters

theorem W1_eq_actual_prime_sum {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) (hXN : X ≤ N) :
    W1 N X = ∑ p ∈ (momentSupport N X).filter Nat.Prime, Real.log p ^ 2 / p := by
  have hs : (primeBases N).filter
      (fun p : Nat => sourceVaughanU N < (p : Real) ∧ (p : Real) ≤ X) =
      (momentSupport N X).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, primeBases, Finset.mem_Icc, mem_momentSupport hN hX]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨⟨h.2.two_le, by exact_mod_cast h.1.2.trans hXN⟩, h.2⟩, h.1⟩
  rw [W1, ← Finset.sum_filter, hs]

theorem mem_exponentsFor_iff {N p e : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hXN : X ≤ N) (hp : p.Prime) :
    e ∈ exponentsFor N X p ↔ 0 < e ∧
      sourceVaughanU N < ((p ^ e : Nat) : Real) ∧ ((p ^ e : Nat) : Real) ≤ X := by
  simp only [exponentsFor, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, exponent_le_cutoff hN hp (h.2.2.trans hXN)⟩, h.2⟩

theorem mem_W2_exponents_iff {N p e : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hXN : X ≤ N) (hp : p.Prime) :
    e ∈ (exponentsFor N X p).filter (2 ≤ ·) ↔
      2 ≤ e ∧ sourceVaughanU N < ((p ^ e : Nat) : Real) ∧
        ((p ^ e : Nat) : Real) ≤ X := by
  rw [Finset.mem_filter, mem_exponentsFor_iff hN hXN hp]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · exact fun h => ⟨⟨by omega, h.2⟩, h.1⟩

theorem mem_W3_exponents_iff {N p e f : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hXN : X ≤ N) (hp : p.Prime) :
    (f ∈ exponentsFor N X p ∧ e ∈ (exponentsFor N X p).filter (· < f)) ↔
      0 < e ∧ e < f ∧ sourceVaughanU N < ((p ^ e : Nat) : Real) ∧
        ((p ^ f : Nat) : Real) ≤ X := by
  simp only [Finset.mem_filter, mem_exponentsFor_iff hN hXN hp]
  constructor
  · exact fun h => ⟨h.2.1.1, h.2.2, h.2.1.2.1, h.1.2.2⟩
  · rintro ⟨he, hef, hU, hX⟩
    have hpow : ((p ^ e : Nat) : Real) < ((p ^ f : Nat) : Real) := by
      exact_mod_cast (pow_lt_pow_iff_right₀ hp.one_lt).2 hef
    exact ⟨⟨he.trans hef, hU.trans hpow, hX⟩,
      ⟨he, hU, hpow.le.trans hX⟩, hef⟩

theorem ordered_max_sum (s : Finset Nat) (F : Nat → Real) :
    (∑ e ∈ s, ∑ f ∈ s, F (max e f)) =
      (∑ e ∈ s, F e) + 2 * (∑ f ∈ s, ∑ _e ∈ s.filter (· < f), F f) := by
  have hpoint (e f : Nat) :
      F (max e f) = (if e = f then F e else 0) +
        (if e < f then F f else 0) + (if f < e then F e else 0) := by
    rcases lt_trichotomy e f with h | h | h
    · simp [max_eq_right h.le, h, h.ne, not_lt_of_ge h.le]
    · simp [h]
    · simp [max_eq_left h.le, h, h.ne', not_lt_of_ge h.le]
  have hd : (∑ e ∈ s, ∑ f ∈ s, if e = f then F e else 0) = ∑ e ∈ s, F e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [he]
  have hswap : (∑ e ∈ s, ∑ f ∈ s, if e < f then F f else 0) =
      ∑ f ∈ s, ∑ e ∈ s, if e < f then F f else 0 := Finset.sum_comm
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [hd, hswap]
  simp only [Finset.sum_filter]
  ring

theorem exponentCutoff_pos {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    1 ≤ exponentCutoff N := by
  apply (Nat.le_floor_iff (mul_nonneg (by norm_num) (sourceL_pos hN).le)).2
  have := sourceL_ge_2000 hN
  norm_num
  linarith

theorem diagonal_sum_split {N p : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    (∑ e ∈ exponentsFor N X p, Real.log p ^ 2 / (p : Real) ^ e) =
      (if sourceVaughanU N < (p : Real) ∧ (p : Real) ≤ X
        then Real.log p ^ 2 / p else 0) +
      ∑ e ∈ (exponentsFor N X p).filter (2 ≤ ·), Real.log p ^ 2 / (p : Real) ^ e := by
  have hpoint (e : Nat) (he : e ∈ exponentsFor N X p) :
      Real.log p ^ 2 / (p : Real) ^ e =
        (if e = 1 then Real.log p ^ 2 / p else 0) +
        (if 2 ≤ e then Real.log p ^ 2 / (p : Real) ^ e else 0) := by
    have he1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 he).1).1
    by_cases h : e = 1
    · simp [h]
    · have : 2 ≤ e := by omega
      simp [h, this]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  simp [Finset.sum_filter, exponentsFor, exponentCutoff_pos hN]

theorem ordered_power_sum_eq_W1_W2_W3 {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    (∑ p ∈ primeBases N, ∑ e ∈ exponentsFor N X p, ∑ f ∈ exponentsFor N X p,
      Real.log p ^ 2 / (p : Real) ^ max e f) = W1 N X + W2 N X + 2 * W3 N X := by
  calc
    _ = ∑ p ∈ primeBases N,
        (((if sourceVaughanU N < (p : Real) ∧ (p : Real) ≤ X
            then Real.log p ^ 2 / p else 0) +
          ∑ e ∈ (exponentsFor N X p).filter (2 ≤ ·),
            Real.log p ^ 2 / (p : Real) ^ e) +
        2 * (∑ f ∈ exponentsFor N X p,
          ∑ _e ∈ (exponentsFor N X p).filter (· < f),
            Real.log p ^ 2 / (p : Real) ^ f)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ordered_max_sum (exponentsFor N X p) (fun e => Real.log p ^ 2 / (p : Real) ^ e),
        diagonal_sum_split hN]
    _ = _ := by simp only [W1, W2, W3, Finset.sum_add_distrib, Finset.mul_sum]

theorem actualMoment_le_613 {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) (hXN : X ≤ N)
    (hXU : X < sourceVaughanU N ^ 2) :
    actualMoment N X ≤ X * (W1 N X + W2 N X + 2 * W3 N X) := by
  simpa only [ordered_power_sum_eq_W1_W2_W3 hN] using
    actualMoment_le_ordered_power_sum hN hX hXN hXU

theorem actualMoment_source_le_613 {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    actualMoment N ((N : Real) / M) ≤
      ((N : Real) / M) * (W1 N ((N : Real) / M) + W2 N ((N : Real) / M) +
        2 * W3 N ((N : Real) / M)) := by
  have hg := source_quotient_geometry hN hM hM'
  exact actualMoment_le_613 (exp_2000_le_of_exp_3100_le hN)
    (div_nonneg (Nat.cast_nonneg N) hg.1.le) hg.2.2.2.2 hg.2.2.2.1

theorem actualMoment_source_high_powers_paid {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    actualMoment N ((N : Real) / M) ≤
      ((N : Real) / M) * (W1 N ((N : Real) / M) + 25876 / 10000 +
        2 * (681 / 10000)) := by
  have hg := source_quotient_geometry hN hM hM'
  have h2 : W2 N ((N : Real) / M) ≤ 25876 / 10000 := W2_le_25876 hN
  have h3 : W3 N ((N : Real) / M) ≤ 681 / 10000 := W3_le_681 hN
  apply (actualMoment_source_le_613 hN hM hM').trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (Nat.cast_nonneg N) hg.1.le)
  exact add_le_add (add_le_add le_rfl h2) (mul_le_mul_of_nonneg_left h3 (by norm_num))

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
