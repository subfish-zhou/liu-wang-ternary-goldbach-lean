import LiuWang.Proof.SmallConductorExpansion.Interval
import LiuWang.Proof.ExceptionalZeroGap.DerivativeTail

/-!
# One-amplitude Abel tails at an aligned period

At a whole-period cutoff the starting character prefix is exactly zero.
The forward Abel identity therefore costs one period amplitude, not two.
No positivity of character prefixes is required.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset Filter
open scoped Topology
open DirichletLConditionalValueSeries DirichletLAbelWeightVariation

namespace LiuWang.Proof.SmallConductorExpansion.Continuation

variable {q : ℕ} [NeZero q]

theorem sum_cutoff_eq_zero (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {m : ℕ} (hm : q ∣ m) : (∑ k ∈ range m, chi k) = 0 := by
  obtain ⟨k, rfl⟩ := hm
  rw [Nat.mul_comm]
  exact DirichletLWeakStripDerivative.sum_mul_period_eq_zero chi hc k

theorem norm_aligned_real_tail_le (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) {P sigma : ℝ}
    (hP : PeriodAmplitude chi P) (hs : 0 < sigma) :
    ‖chi.LFunction (sigma : ℂ) -
      ∑ k ∈ range m, cpowWeight (sigma : ℂ) k * chi k‖ ≤ P * (m : ℝ) ^ (-sigma) := by
  have hstart := sum_cutoff_eq_zero chi hc hqm
  have hlim := tendsto_sum_range_orderedValueSeries chi hc (sigma : ℂ) hs
  rw [orderedValueSeries_eq_LFunction_of_re_pos] at hlim
  have hweight (k : ℕ) : cpowWeight (sigma : ℂ) k = (((k : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
    rw [cpowWeight, show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by simp,
      ← Complex.ofReal_cpow (Nat.cast_nonneg k)]
  apply le_of_tendsto ((hlim.sub_const _).norm)
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [← sum_Ico_eq_sub _ hn]
  simp only [hweight]
  calc
    _ ≤ (m : ℝ) ^ (-sigma) * P := by
      apply LiuWang.Proof.ExceptionalZeroGap.norm_sum_weighted_Ico_le _ _ hn
      · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      · intro i hi j hj hij
        have him : m ≤ i := hi.1
        have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
        exact Real.rpow_le_rpow_of_nonpos hi0 (by exact_mod_cast hij) (by linarith)
      · intro k hk
        rw [sum_Ico_eq_sub _ hk.1, hstart, sub_zero]
        exact norm_prefix_le chi hc hP k
    _ = _ := mul_comm _ _

def AlignedCertificate (chi : DirichletCharacter ℂ q) (m : ℕ) (P C : ℝ) : Prop :=
  PeriodAmplitude chi P ∧
    C * negativeHarmonic chi m + P * C / m < positiveHarmonic chi m

theorem alignedCertificate_ne_zero (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) {P C sigma : ℝ}
    (hcert : AlignedCertificate chi m P C) (hs0 : 0 < sigma) (hs1 : sigma ≤ 1)
    (hC : (m : ℝ) ^ (1 - sigma) ≤ C) : chi.LFunction (sigma : ℂ) ≠ 0 := by
  have hP0 : 0 ≤ P := by simpa using norm_prefix_le chi hc hcert.1 0
  have ht := norm_aligned_real_tail_le chi hc hm hqm hcert.1 hs0
  have he (k : ℕ) : (cpowWeight (sigma : ℂ) k * chi k).re =
      (k : ℝ) ^ (-sigma) * (chi k).re := by
    rw [cpowWeight, show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by simp,
      ← Complex.ofReal_cpow (Nat.cast_nonneg k)]
    simp
  have hr := Complex.abs_re_le_norm
    (chi.LFunction (sigma : ℂ) - ∑ k ∈ range m, cpowWeight (sigma : ℂ) k * chi k)
  simp only [Complex.sub_re, Complex.re_sum, he] at hr
  have ht' : P * (m : ℝ) ^ (-sigma) ≤ P * C / m := by
    calc
      _ ≤ P * (C / m) :=
        mul_le_mul_of_nonneg_left (real_weight_bounds hm hs1 hC hm le_rfl).2 hP0
      _ = _ := by ring
  have hl := real_partialSum_ge_signed chi hc hm hs1 hC
  have hh := (abs_le.mp (hr.trans (ht.trans ht'))).1
  intro hz
  rw [hz, Complex.zero_re] at hh
  have hpos := hcert.2
  linarith

theorem alignedCertificate_ne_zero_on_interval (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {m n : ℕ} (hm : 1 ≤ m) (hqm : q ∣ m) (hn : 1 < n)
    {P C beta : ℝ} (hcert : AlignedCertificate chi m P C)
    (hC : 0 ≤ C) (hpow : (m : ℝ) ≤ C ^ n)
    (hb : 1 - 1 / (n : ℝ) ≤ beta) : chi.LFunction (beta : ℂ) ≠ 0 := by
  by_cases hb1 : 1 ≤ beta
  · exact chi.LFunction_ne_zero_of_one_le_re (Or.inl hc) hb1
  · apply alignedCertificate_ne_zero chi hc hm hqm hcert
    · have hnR : (1 : ℝ) < n := by exact_mod_cast hn
      have hi : 1 / (n : ℝ) < 1 := (div_lt_one (by linarith)).mpr hnR
      linarith
    · exact (lt_of_not_ge hb1).le
    · exact rpow_envelope_of_pow hm (by omega) hC hpow hb

end LiuWang.Proof.SmallConductorExpansion.Continuation
