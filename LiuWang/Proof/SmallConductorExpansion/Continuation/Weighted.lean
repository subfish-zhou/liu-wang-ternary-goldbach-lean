import LiuWang.Proof.SmallConductorExpansion.Continuation.AlignedTables
import Mathlib.Data.Nat.Log

/-!
# Termwise dyadic rational envelopes

Negative coefficients are charged at their own integer argument, not at the
largest truncation weight. This preserves substantially more signed
cancellation while retaining an entirely rational finite certificate.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset
open DirichletLConditionalValueSeries DirichletLAbelWeightVariation

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

def weightedNegative {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (m : ℕ) (C : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range m, C k * max (-(chi k).re) 0 / k

theorem real_partialSum_ge_weighted {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) {m : ℕ}
    {sigma : ℝ} {C : ℕ → ℝ} (hs : sigma ≤ 1)
    (hC : ∀ k, 1 ≤ k → k ≤ m → (k : ℝ) ^ (1 - sigma) ≤ C k) :
    positiveHarmonic chi m - weightedNegative chi m C ≤
      ∑ k ∈ range m, (k : ℝ) ^ (-sigma) * (chi k).re := by
  unfold positiveHarmonic weightedNegative
  rw [← sum_sub_distrib]
  apply sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    rw [character_nat_zero_of_ne_one chi hc]
    simp
  · have hk1 : 1 ≤ k := by omega
    have hw := real_weight_bounds hk1 hs (hC k hk1 (mem_range.mp hk).le) hk1 le_rfl
    by_cases hp : 0 ≤ (chi k).re
    · rw [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]
      simp only [mul_zero, zero_div, sub_zero]
      simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hw.1 hp
    · have hn := (lt_of_not_ge hp).le
      rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
      simp only [zero_div, zero_sub]
      have hh := mul_le_mul_of_nonpos_right hw.2 hn
      convert hh using 1
      ring

theorem weighted_ne_zero {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) {m : ℕ}
    (hm : 1 ≤ m) (hqm : q ∣ m) {P sigma : ℝ} {C : ℕ → ℝ}
    (hP : PeriodAmplitude chi P) (hs0 : 0 < sigma) (hs1 : sigma ≤ 1)
    (hC : ∀ k, 1 ≤ k → k ≤ m → (k : ℝ) ^ (1 - sigma) ≤ C k)
    (hcert : weightedNegative chi m C + P * C m / m < positiveHarmonic chi m) :
    chi.LFunction (sigma : ℂ) ≠ 0 := by
  have hP0 : 0 ≤ P := by simpa using norm_prefix_le chi hc hP 0
  have ht := norm_aligned_real_tail_le chi hc hm hqm hP hs0
  have he (k : ℕ) : (cpowWeight (sigma : ℂ) k * chi k).re =
      (k : ℝ) ^ (-sigma) * (chi k).re := by
    rw [cpowWeight, show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by simp,
      ← Complex.ofReal_cpow (Nat.cast_nonneg k)]
    simp
  have hr := Complex.abs_re_le_norm
    (chi.LFunction (sigma : ℂ) - ∑ k ∈ range m, cpowWeight (sigma : ℂ) k * chi k)
  simp only [Complex.sub_re, Complex.re_sum, he] at hr
  have ht' : P * (m : ℝ) ^ (-sigma) ≤ P * C m / m := by
    calc
      _ ≤ P * (C m / m) :=
        mul_le_mul_of_nonneg_left (real_weight_bounds hm hs1 (hC m hm le_rfl) hm le_rfl).2 hP0
      _ = _ := by ring
  have hl := real_partialSum_ge_weighted chi hc hs1 hC
  have hh := (abs_le.mp (hr.trans (ht.trans ht'))).1
  intro hz
  rw [hz, Complex.zero_re] at hh
  linarith

def dyadicEnvelope (A : ℚ) (k : ℕ) : ℚ := A ^ Nat.clog 2 k

theorem dyadicEnvelope_pow_lower {A : ℚ} {n : ℕ}
    (hpow : 2 ≤ A ^ n) (k : ℕ) : (k : ℚ) ≤ dyadicEnvelope A k ^ n := by
  have hk : (k : ℚ) ≤ (2 : ℚ) ^ Nat.clog 2 k := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) k
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hpow (Nat.clog 2 k)
  calc
    _ ≤ (2 : ℚ) ^ Nat.clog 2 k := hk
    _ ≤ (A ^ n) ^ Nat.clog 2 k := hp
    _ = _ := by unfold dyadicEnvelope; rw [← pow_mul, ← pow_mul, Nat.mul_comm]

def RationalWeightedCertificate (q : ℕ) (values : List ℤ) (m : ℕ) (P A : ℚ) : Prop :=
  (∀ n ∈ range q, |((∑ k ∈ range n, tableValue q values k : ℤ) : ℚ)| ≤ P) ∧
    (∑ k ∈ range m, dyadicEnvelope A k * (max (-(tableValue q values k)) 0 : ℚ) / k) +
      P * dyadicEnvelope A m / m <
      ∑ k ∈ range m, (max (tableValue q values k) 0 : ℚ) / k

theorem rationalWeighted_original_region {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (values : List ℤ)
    (hvalues : ∀ a : ZMod q, chi a = (values.getD a.val 0 : ℂ))
    {m n : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) (hn : 1 < n)
    {P A : ℚ} (hcert : RationalWeightedCertificate q values m P A)
    (hA : 0 ≤ A) (hpow : 2 ≤ A ^ n)
    {x beta : ℝ} (hlog : (n : ℝ) ≤ 9.645908801 * Real.log x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases hb1 : 1 ≤ beta
  · exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) hb1
  have hval := tableValue_character chi values hvalues
  have hre (k : ℕ) : (chi k).re = (tableValue q values k : ℝ) := by
    rw [hval]
    simp
  have hP : PeriodAmplitude chi (P : ℝ) := by
    intro k hk
    have hh := hcert.1 k (mem_range.mpr hk)
    have he : (∑ j ∈ range k, chi j) = ((∑ j ∈ range k, tableValue q values j : ℤ) : ℂ) := by
      simp only [hval, Int.cast_sum]
    rw [he, Complex.norm_intCast]
    exact_mod_cast hh
  have hbeta := original_region_of_log_scale hn hlog hb
  apply weighted_ne_zero chi hc hm hqm hP (C := fun k => (dyadicEnvelope A k : ℝ))
  · have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have hi : 1 / (n : ℝ) < 1 := (div_lt_one (by linarith)).mpr hnR
    linarith
  · exact (lt_of_not_ge hb1).le
  · intro k hk _
    exact rpow_envelope_of_pow hk (by omega)
      (by exact_mod_cast (pow_nonneg hA (Nat.clog 2 k)))
      (by exact_mod_cast dyadicEnvelope_pow_lower hpow k) hbeta
  · unfold weightedNegative positiveHarmonic
    simp only [hre]
    exact_mod_cast hcert.2

end LiuWang.Proof.SmallConductorExpansion.Continuation
