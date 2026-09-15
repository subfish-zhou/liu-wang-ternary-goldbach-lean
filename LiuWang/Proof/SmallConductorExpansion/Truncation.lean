import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrefixBoundedHarmonicTail
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Signed finite certificates with an absolute Abel tail

The finite test retains positive and negative character values separately.
It allows arbitrary signs of character prefixes. The supplied amplitude is
checked only on one period; it bounds every natural prefix by periodicity.
The analytic tail is that of the original naturally ordered L-function.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset
open DirichletLConditionalValueSeries DirichletLAbelWeightVariation

namespace LiuWang.Proof.SmallConductorExpansion

variable {q : ℕ} [NeZero q]

def PeriodAmplitude (chi : DirichletCharacter ℂ q) (P : ℝ) : Prop :=
  ∀ n < q, ‖∑ k ∈ range n, chi k‖ ≤ P

theorem norm_prefix_le (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {P : ℝ} (hP : PeriodAmplitude chi P) (n : ℕ) :
    ‖∑ k ∈ range n, chi k‖ ≤ P := by
  have hn : n = (n / q) * q + n % q := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n q).symm
  have he : (∑ k ∈ range n, chi k) = ∑ k ∈ range (n % q), chi k := by
    conv_lhs => rw [hn, sum_range_add,
      DirichletLWeakStripDerivative.sum_mul_period_eq_zero chi hc, zero_add]
    apply sum_congr rfl
    intro k _
    simp
  rw [he]
  exact hP _ (Nat.mod_lt _ (NeZero.pos q))

def positiveHarmonic (chi : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, max (chi k).re 0 / k

def negativeHarmonic (chi : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, max (-(chi k).re) 0 / k

def SignedCertificate (chi : DirichletCharacter ℂ q) (m : ℕ) (P C : ℝ) : Prop :=
  PeriodAmplitude chi P ∧
    C * negativeHarmonic chi m + 2 * P * C / m < positiveHarmonic chi m

theorem real_weight_bounds {sigma C : ℝ} {m k : ℕ} (hm : 1 ≤ m)
    (hs : sigma ≤ 1) (hC : (m : ℝ) ^ (1 - sigma) ≤ C)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    (k : ℝ)⁻¹ ≤ (k : ℝ) ^ (-sigma) ∧
      (k : ℝ) ^ (-sigma) ≤ C / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : (k : ℝ) ^ (-sigma) = (k : ℝ) ^ (1 - sigma) / k := by
    rw [← Real.rpow_sub_one hk0.ne']
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  · rw [he]
    apply div_le_div_of_nonneg_right _ hk0.le
    exact (Real.rpow_le_rpow hk0.le (by exact_mod_cast hkm) (by linarith)).trans hC

theorem real_partialSum_ge_signed (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) {sigma C : ℝ} (hs : sigma ≤ 1)
    (hC : (m : ℝ) ^ (1 - sigma) ≤ C) :
    positiveHarmonic chi m - C * negativeHarmonic chi m ≤
      ∑ k ∈ range m, (k : ℝ) ^ (-sigma) * (chi k).re := by
  unfold positiveHarmonic negativeHarmonic
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    rw [character_nat_zero_of_ne_one chi hc]
    simp
  · have hw := real_weight_bounds hm hs hC (by omega) (mem_range.mp hk).le
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    by_cases hp : 0 ≤ (chi k).re
    · rw [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]
      simp only [zero_div, mul_zero, sub_zero]
      simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hw.1 hp
    · have hn := (lt_of_not_ge hp).le
      rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
      simp only [zero_div, zero_sub]
      have hh := mul_le_mul_of_nonpos_right hw.2 hn
      convert hh using 1
      ring

theorem real_LFunction_lower (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) {P C sigma : ℝ}
    (hP : PeriodAmplitude chi P) (hs0 : 0 < sigma) (hs1 : sigma ≤ 1)
    (hC : (m : ℝ) ^ (1 - sigma) ≤ C) :
    positiveHarmonic chi m - C * negativeHarmonic chi m - 2 * P * C / m ≤
      (chi.LFunction (sigma : ℂ)).re := by
  have hP0 : 0 ≤ P := by simpa using norm_prefix_le chi hc hP 0
  have ht := chi.norm_LFunction_sub_sum_le_of_prefix_bound hc (sigma : ℂ) hs0 P
    (norm_prefix_le chi hc hP) hm
  have he (k : ℕ) : (cpowWeight (sigma : ℂ) k * chi k).re =
      (k : ℝ) ^ (-sigma) * (chi k).re := by
    rw [cpowWeight, show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by simp,
      ← Complex.ofReal_cpow (Nat.cast_nonneg k)]
    simp
  have hr := Complex.abs_re_le_norm
    (chi.LFunction (sigma : ℂ) - ∑ k ∈ range m, cpowWeight (sigma : ℂ) k * chi k)
  simp only [Complex.sub_re, Complex.re_sum, he] at hr
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs0, div_self hs0.ne', one_mul] at ht
  have hw := (real_weight_bounds hm hs1 hC hm le_rfl).2
  have ht' : P * ((m : ℝ) ^ (-sigma) + (m : ℝ) ^ (-sigma)) ≤ 2 * P * C / m := by
    calc
      _ ≤ P * (C / m + C / m) := mul_le_mul_of_nonneg_left (add_le_add hw hw) hP0
      _ = _ := by ring
  have hl := real_partialSum_ge_signed chi hc hm hs1 hC
  have hh := (abs_le.mp (hr.trans (ht.trans ht'))).1
  linarith

theorem LFunction_ne_zero_of_signedCertificate (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {m : ℕ} (hm : 1 ≤ m) {P C sigma : ℝ}
    (hcert : SignedCertificate chi m P C) (hs0 : 0 < sigma)
    (hs1 : sigma ≤ 1) (hC : (m : ℝ) ^ (1 - sigma) ≤ C) :
    chi.LFunction (sigma : ℂ) ≠ 0 := by
  intro hz
  have hl := real_LFunction_lower chi hc hm hcert.1 hs0 hs1 hC
  rw [hz, Complex.zero_re] at hl
  have hh := hcert.2
  linarith

end LiuWang.Proof.SmallConductorExpansion
