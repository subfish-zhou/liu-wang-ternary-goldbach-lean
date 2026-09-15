import LiuWang.Proof.ArithmeticBounds.LambdaMoment.HighPowers

/-! 从真实约数对到同底有序素幂对；再以倍数计数支付 (6.13) 的系数。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

open scoped BigOperators
open Parameters

theorem mem_powerIndices_iff {N p e : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hXN : X ≤ N) :
    (p, e) ∈ powerIndices N X ↔ p.Prime ∧ 0 < e ∧
      sourceVaughanU N < ((p ^ e : Nat) : Real) ∧ ((p ^ e : Nat) : Real) ≤ X := by
  simp only [powerIndices, Finset.mem_filter, Finset.mem_product, primeBases,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_, hp⟩, he⟩, hU, hX⟩
    exact ⟨hp, he.1, hU, hX⟩
  · rintro ⟨hp, he, hU, hX⟩
    have hpN : p ≤ N :=
      (Nat.le_pow he).trans (by exact_mod_cast hX.trans hXN)
    exact ⟨⟨⟨⟨hp.two_le, hpN⟩, hp⟩, he, exponent_le_cutoff hN hp (hX.trans hXN)⟩,
      hU, hX⟩

theorem powerIndices_injective {N : Nat} {X : Real} :
    Set.InjOn (fun i : Nat × Nat => i.1 ^ i.2) (powerIndices N X : Set (Nat × Nat)) := by
  rintro ⟨p, e⟩ hi ⟨q, f⟩ hj heq
  have hi' := (Finset.mem_product.1 (Finset.mem_filter.1 hi).1)
  have hj' := (Finset.mem_product.1 (Finset.mem_filter.1 hj).1)
  have hp := (Finset.mem_filter.1 hi'.1).2
  have hq := (Finset.mem_filter.1 hj'.1).2
  have he : e ≠ 0 := by have := (Finset.mem_Icc.1 hi'.2).1; omega
  have hf : f ≠ 0 := by have := (Finset.mem_Icc.1 hj'.2).1; omega
  have hpq : p = q := by
    simpa only [hp.pow_minFac he, hq.pow_minFac hf] using congrArg Nat.minFac heq
  subst q
  have hef : e = f := pow_right_injective₀ hp.pos hp.ne_one heq
  subst f
  rfl

theorem sum_largeDivisors_eq_powerIndices {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) (hXN : X ≤ N)
    (F : Nat → Real) (hF : ∀ r, ¬IsPrimePow r → F r = 0) :
    (∑ r ∈ largeDivisors N X, F r) =
      ∑ i ∈ powerIndices N X, F (i.1 ^ i.2) := by
  calc
    _ = ∑ r ∈ (largeDivisors N X).filter IsPrimePow, F r := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : IsPrimePow r
      · simp [h]
      · simp [h, hF r h]
    _ = _ := by
      symm
      refine Finset.sum_bij (fun i _ => i.1 ^ i.2) ?_ ?_ ?_ (by intros; rfl)
      · rintro ⟨p, e⟩ hi
        have hm := (mem_powerIndices_iff hN hXN).1 hi
        have hpp := (isPrimePow_nat_iff (p ^ e)).2 ⟨p, e, hm.1, hm.2.1, rfl⟩
        simp only [Finset.mem_filter, largeDivisors, Finset.mem_Icc]
        exact ⟨⟨⟨hpp.pos, (Nat.le_floor_iff hX).2 hm.2.2.2⟩, hm.2.2.1⟩, hpp⟩
      · intro i hi j hj heq
        exact powerIndices_injective hi hj heq
      · intro r hr
        have hr' := Finset.mem_filter.1 hr
        have hm := Finset.mem_filter.1 hr'.1
        obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff r).1 hr'.2
        exact ⟨(p, e), (mem_powerIndices_iff hN hXN).2
          ⟨hp, he, hm.2, (Nat.le_floor_iff hX).1 (Finset.mem_Icc.1 hm.1).2⟩, rfl⟩

theorem sum_powerIndices (N : Nat) (X : Real) (F : Nat → Nat → Real) :
    (∑ i ∈ powerIndices N X, F i.1 i.2) =
      ∑ p ∈ primeBases N, ∑ e ∈ exponentsFor N X p, F p e := by
  simp only [powerIndices, exponentsFor, Finset.sum_filter, Finset.sum_product]

theorem actualMoment_eq_prime_power_pairs {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) (hXN : X ≤ N) :
    actualMoment N X =
      ∑ p ∈ primeBases N, ∑ e ∈ exponentsFor N X p,
        ∑ q ∈ primeBases N, ∑ f ∈ exponentsFor N X q,
          Real.log p * Real.log q *
            ((pairMultiples N X (p ^ e) (q ^ f)).card : Real) := by
  rw [actualMoment_eq_ordered_divisor_pairs,
    sum_largeDivisors_eq_powerIndices hN hX hXN _ (by
      intro r hr
      simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hr])]
  calc
    _ = ∑ i ∈ powerIndices N X, ∑ j ∈ powerIndices N X,
        ArithmeticFunction.vonMangoldt (i.1 ^ i.2) *
          ArithmeticFunction.vonMangoldt (j.1 ^ j.2) *
            ((pairMultiples N X (i.1 ^ i.2) (j.1 ^ j.2)).card : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_largeDivisors_eq_powerIndices hN hX hXN _ (by
        intro r hr
        simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hr])
    _ = ∑ i ∈ powerIndices N X, ∑ j ∈ powerIndices N X,
        Real.log i.1 * Real.log j.1 *
          ((pairMultiples N X (i.1 ^ i.2) (j.1 ^ j.2)).card : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hi' := (mem_powerIndices_iff hN hXN).1 hi
      have hj' := (mem_powerIndices_iff hN hXN).1 hj
      rw [ArithmeticFunction.vonMangoldt_apply_pow hi'.2.1.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hi'.1,
        ArithmeticFunction.vonMangoldt_apply_pow hj'.2.1.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hj'.1]
    _ = _ := by
      rw [sum_powerIndices N X (fun p e => ∑ j ∈ powerIndices N X,
        Real.log p * Real.log j.1 * ((pairMultiples N X (p ^ e) (j.1 ^ j.2)).card : Real))]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro e he
      exact sum_powerIndices N X (fun q f =>
        Real.log p * Real.log q * ((pairMultiples N X (p ^ e) (q ^ f)).card : Real))

theorem pairMultiples_distinct_primes {N p q e f : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X)
    (hXU : X < sourceVaughanU N ^ 2) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : e ∈ exponentsFor N X p) (hf : f ∈ exponentsFor N X q) :
    pairMultiples N X (p ^ e) (q ^ f) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro m hm
  have hm' := Finset.mem_filter.1 hm
  have hmr := (mem_momentSupport hN hX).1 hm'.1
  exact large_divisors_not_coprime (sourceVaughanU_pos hN).le hXU
    (Finset.mem_filter.1 he).2.1 (Finset.mem_filter.1 hf).2.1 hmr.2
    (by have := (Finset.mem_Ioc.1 hm'.1).1; omega) hm'.2.1 hm'.2.2
    (Nat.coprime_pow_primes e f hp hq hpq)

theorem actualMoment_eq_same_prime_pairs {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) (hXN : X ≤ N)
    (hXU : X < sourceVaughanU N ^ 2) :
    actualMoment N X =
      ∑ p ∈ primeBases N, ∑ e ∈ exponentsFor N X p,
        ∑ f ∈ exponentsFor N X p,
          Real.log p ^ 2 * ((pairMultiples N X (p ^ e) (p ^ f)).card : Real) := by
  rw [actualMoment_eq_prime_power_pairs hN hX hXN]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single p]
  · simp only [pow_two]
  · intro q hq hqp
    apply Finset.sum_eq_zero
    intro f hf
    rw [pairMultiples_distinct_primes hN hX hXU (Finset.mem_filter.1 hp).2
      (Finset.mem_filter.1 hq).2 (Ne.symm hqp) he hf]
    simp
  · exact fun h => (h hp).elim

theorem pairMultiples_card_le {N p e f : Nat} {X : Real}
    (hX : 0 ≤ X) (hp : 0 < p) :
    ((pairMultiples N X (p ^ e) (p ^ f)).card : Real) ≤
      X / (p : Real) ^ max e f := by
  have hd : 0 < p ^ max e f := pow_pos hp _
  have hsub : pairMultiples N X (p ^ e) (p ^ f) ⊆
      (Finset.Icc 1 ⌊X⌋₊).filter (fun m => p ^ max e f ∣ m) := by
    intro m hm
    have hm' := Finset.mem_filter.1 hm
    have hmi := Finset.mem_Ioc.1 hm'.1
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hmi.2⟩, ?_⟩
    rcases le_total e f with h | h
    · simpa only [max_eq_right h] using hm'.2.2
    · simpa only [max_eq_left h] using hm'.2.1
  calc
    _ ≤ (((Finset.Icc 1 ⌊X⌋₊).filter (fun m => p ^ max e f ∣ m)).card : Real) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ((⌊X⌋₊ / p ^ max e f : Nat) : Real) := by
      have := AnalyticNumberTheory.LargeSieve.sum_dvd_indicator_Icc ⌊X⌋₊ (p ^ max e f) hd
      simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using this
    _ = (⌊X / ((p ^ max e f : Nat) : Real)⌋₊ : Real) := by
      rw [Nat.floor_div_natCast]
    _ ≤ X / (p : Real) ^ max e f := by
      simpa only [Nat.cast_pow] using
        Nat.floor_le (show 0 ≤ X / ((p ^ max e f : Nat) : Real) by positivity)

theorem actualMoment_le_ordered_power_sum {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) (hXN : X ≤ N)
    (hXU : X < sourceVaughanU N ^ 2) :
    actualMoment N X ≤ X *
      (∑ p ∈ primeBases N, ∑ e ∈ exponentsFor N X p, ∑ f ∈ exponentsFor N X p,
        Real.log p ^ 2 / (p : Real) ^ max e f) := by
  rw [actualMoment_eq_same_prime_pairs hN hX hXN hXU]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro e he
  apply Finset.sum_le_sum
  intro f hf
  calc
    _ ≤ Real.log p ^ 2 * (X / (p : Real) ^ max e f) :=
      mul_le_mul_of_nonneg_left (pairMultiples_card_le hX (Finset.mem_filter.1 hp).2.pos)
        (sq_nonneg _)
    _ = _ := by ring

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
