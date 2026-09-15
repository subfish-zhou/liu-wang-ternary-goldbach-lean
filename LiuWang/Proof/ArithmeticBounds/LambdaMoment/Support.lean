import LiuWang.Proof.ArithmeticBounds.ContinuationConsumer
import Mathlib.Analysis.Complex.ExponentialBounds

/-! 实际大约数权的平方展开、严格端点和同素数底支持。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

open scoped BigOperators
open Parameters

def momentSupport (N : Nat) (X : Real) : Finset Nat :=
  Finset.Ioc ⌊sourceVaughanU N⌋₊ ⌊X⌋₊

def actualMoment (N : Nat) (X : Real) : Real :=
  ∑ m ∈ momentSupport N X, sourceLargeDivisorWeight N m ^ 2

def largeDivisors (N : Nat) (X : Real) : Finset Nat :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun r => sourceVaughanU N < (r : Real))

def pairMultiples (N : Nat) (X : Real) (r s : Nat) : Finset Nat :=
  (momentSupport N X).filter (fun m => r ∣ m ∧ s ∣ m)

theorem mem_momentSupport {N m : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) (hX : 0 ≤ X) :
    m ∈ momentSupport N X ↔ sourceVaughanU N < (m : Real) ∧ (m : Real) ≤ X := by
  simp only [momentSupport, Finset.mem_Ioc, Nat.floor_lt (sourceVaughanU_pos hN).le,
    Nat.le_floor_iff hX]

theorem source_quotient_geometry {N : Nat} {M : Real}
    (hN : Real.exp 3100 ≤ (N : Real))
    (hM : sourceVaughanV N ≤ M) (hM' : M ≤ (N : Real) / sourceVaughanU N) :
    0 < M ∧ sourceVaughanU N ≤ (N : Real) / M ∧
      (N : Real) / M ≤ (N : Real) / sourceVaughanV N ∧
      (N : Real) / M < sourceVaughanU N ^ 2 ∧ (N : Real) / M ≤ N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hu := sourceVaughanU_pos hn
  have hv := sourceVaughanV_pos hn
  have hm := hv.trans_le hM
  have hx := div_le_div_of_nonneg_left (natCast_pos_of_exp_le hN).le hv hM
  have hsq : (N : Real) / sourceVaughanV N < sourceVaughanU N ^ 2 :=
    (div_lt_iff₀ hv).2 (natCast_lt_sourceVaughanU_sq_mul_V hn)
  refine ⟨hm, ?_, hx, hx.trans_lt hsq, ?_⟩
  · apply (le_div_iff₀ hm).2
    have := (le_div_iff₀ hu).1 hM'
    nlinarith
  · exact div_le_self (Nat.cast_nonneg N)
      ((one_lt_sourceVaughanU hn).le.trans ((sourceVaughanU_le_V hn).trans hM))

theorem source_weight_eq_sum_largeDivisors {N m : Nat} {X : Real}
    (hm : 0 < m) (hmX : m ≤ ⌊X⌋₊) :
    sourceLargeDivisorWeight N m =
      ∑ r ∈ largeDivisors N X, if r ∣ m then ArithmeticFunction.vonMangoldt r else 0 := by
  have he :
      m.divisors.filter (fun r : Nat => sourceVaughanU N < (r : Real)) =
        (largeDivisors N X).filter (fun r => r ∣ m) := by
    ext r
    simp only [Finset.mem_filter, Nat.mem_divisors, largeDivisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hr, _⟩, hU⟩
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hr hm, (Nat.le_of_dvd hm hr).trans hmX⟩, hU⟩, hr⟩
    · rintro ⟨⟨_, hU⟩, hr⟩
      exact ⟨⟨hr, hm.ne'⟩, hU⟩
  rw [sourceLargeDivisorWeight, he, Finset.sum_filter]

theorem actualMoment_eq_ordered_divisor_pairs {N : Nat} {X : Real} :
    actualMoment N X =
      ∑ r ∈ largeDivisors N X, ∑ s ∈ largeDivisors N X,
        ArithmeticFunction.vonMangoldt r * ArithmeticFunction.vonMangoldt s *
          ((pairMultiples N X r s).card : Real) := by
  unfold actualMoment
  have hw (m : Nat) (hm : m ∈ momentSupport N X) :
      sourceLargeDivisorWeight N m =
        ∑ r ∈ largeDivisors N X,
          if r ∣ m then ArithmeticFunction.vonMangoldt r else 0 :=
    source_weight_eq_sum_largeDivisors
      (by have := (Finset.mem_Ioc.1 hm).1; omega) (Finset.mem_Ioc.1 hm).2
  rw [Finset.sum_congr rfl (fun m hm => congrArg (fun x : Real => x ^ 2) (hw m hm))]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  calc
    _ = ∑ m ∈ momentSupport N X,
        if r ∣ m ∧ s ∣ m then
          ArithmeticFunction.vonMangoldt r * ArithmeticFunction.vonMangoldt s else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      split_ifs <;> simp_all [mul_comm]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [pairMultiples, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem large_divisors_not_coprime {U X : Real} {m r s : Nat}
    (hU : 0 ≤ U) (hX : X < U ^ 2)
    (hr : U < (r : Real)) (hs : U < (s : Real))
    (hm : (m : Real) ≤ X) (hm0 : 0 < m) (hrm : r ∣ m) (hsm : s ∣ m) :
    ¬Nat.Coprime r s := by
  intro hc
  have hd := Nat.le_of_dvd hm0 (hc.mul_dvd_of_dvd_of_dvd hrm hsm)
  have hd' : (r : Real) * (s : Real) ≤ (m : Real) := by exact_mod_cast hd
  have hp : U ^ 2 < (r : Real) * (s : Real) := by
    nlinarith [mul_pos (sub_pos.2 hr) (sub_pos.2 hs)]
  linarith

theorem nonzero_pair_same_prime {U X : Real} {m r s : Nat}
    (hU : 0 ≤ U) (hX : X < U ^ 2)
    (hr : U < (r : Real)) (hs : U < (s : Real))
    (hm : (m : Real) ≤ X) (hm0 : 0 < m) (hrm : r ∣ m) (hsm : s ∣ m)
    (hrΛ : ArithmeticFunction.vonMangoldt r ≠ 0)
    (hsΛ : ArithmeticFunction.vonMangoldt s ≠ 0) :
    ∃ p e f : Nat, p.Prime ∧ 0 < e ∧ 0 < f ∧ r = p ^ e ∧ s = p ^ f := by
  obtain ⟨p, e, hp, he, rfl⟩ :=
    (isPrimePow_nat_iff r).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hrΛ)
  obtain ⟨q, f, hq, hf, rfl⟩ :=
    (isPrimePow_nat_iff s).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hsΛ)
  have hpq : p = q := by
    by_contra hne
    exact large_divisors_not_coprime hU hX hr hs hm hm0 hrm hsm
      (Nat.coprime_pow_primes e f hp hq hne)
  subst q
  exact ⟨p, e, f, hp, he, hf, rfl, rfl⟩

def exponentCutoff (N : Nat) : Nat := ⌊2 * Interfaces.sourceL N⌋₊

def primeBases (N : Nat) : Finset Nat :=
  (Finset.Icc 2 N).filter Nat.Prime

def powerIndices (N : Nat) (X : Real) : Finset (Nat × Nat) :=
  ((primeBases N) ×ˢ Finset.Icc 1 (exponentCutoff N)).filter
    (fun i => sourceVaughanU N < ((i.1 ^ i.2 : Nat) : Real) ∧
      ((i.1 ^ i.2 : Nat) : Real) ≤ X)

theorem exponent_le_cutoff {N p e : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hp : p.Prime)
    (hpe : ((p ^ e : Nat) : Real) ≤ N) :
    e ≤ exponentCutoff N := by
  apply (Nat.le_floor_iff (mul_nonneg (by norm_num) (sourceL_pos hN).le)).2
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hlogp : (1 / 2 : Real) ≤ Real.log p :=
    (show (1 / 2 : Real) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le))
  have hl := Real.log_le_log (pow_pos hp0 e) (by simpa only [Nat.cast_pow] using hpe)
  rw [Real.log_pow] at hl
  change (e : Real) ≤ 2 * Interfaces.sourceL N
  change (e : Real) * Real.log p ≤ Interfaces.sourceL N at hl
  nlinarith [mul_nonneg (Nat.cast_nonneg e) (sub_nonneg.2 hlogp)]

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
