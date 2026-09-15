import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries

/-!
# A finite certificate for actual Dirichlet L-values

Nonnegative real parts of the character's prefix sums in one period imply
`re L(s, chi) >= 1 - 2^(-s) > 0` for every real `s > 0`.
The certificate checks character values, not just the integer modulus.
Natural-order conditional convergence identifies the limit with the original
`LFunction`; no rearrangement or zero-free hypothesis is used.
-/

set_option autoImplicit false
noncomputable section

open Complex Finset Filter
open scoped Topology
open DirichletLConditionalValueSeries DirichletLAbelWeightVariation

namespace LiuWang.Proof.SmallConductorExclusion

variable {q : ℕ} [NeZero q]

def characterPrefix (chi : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (chi k).re

def PeriodPrefixNonnegative (chi : DirichletCharacter ℂ q) : Prop :=
  ∀ n < q, 0 ≤ characterPrefix chi n

theorem prefix_mod (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1) (n : ℕ) :
    characterPrefix chi n = characterPrefix chi (n % q) := by
  have hn : n = (n / q) * q + n % q := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n q).symm
  have he : (∑ k ∈ range n, chi k) = ∑ k ∈ range (n % q), chi k := by
    conv_lhs => rw [hn, sum_range_add,
      DirichletLWeakStripDerivative.sum_mul_period_eq_zero chi hc, zero_add]
    apply sum_congr rfl
    intro k _
    simp
  simpa [characterPrefix, Complex.re_sum] using congrArg Complex.re he

theorem prefix_nonneg (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hcert : PeriodPrefixNonnegative chi) (n : ℕ) : 0 ≤ characterPrefix chi n := by
  rw [prefix_mod chi hc n]
  exact hcert _ (Nat.mod_lt _ (NeZero.pos q))

theorem real_partialSum_lower (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    (hcert : PeriodPrefixNonnegative chi) {sigma : ℝ} (hs : 0 < sigma)
    {n : ℕ} (hn : 3 ≤ n) :
    1 - (2 : ℝ) ^ (-sigma) ≤
      ∑ k ∈ range n, (k : ℝ) ^ (-sigma) * (chi k).re := by
  have hzero : chi 0 = 0 := by
    simpa only [Nat.cast_zero] using character_nat_zero_of_ne_one chi hc
  have hp1 : characterPrefix chi 1 = 0 := by simp [characterPrefix, hzero]
  have hp2 : characterPrefix chi 2 = 1 := by
    simp [characterPrefix, sum_range_succ, hzero]
  have hdiff (i : ℕ) (hi : i ∈ Ico 1 (n - 1)) :
      0 ≤ ((i : ℝ) ^ (-sigma) - (i + 1 : ℝ) ^ (-sigma)) *
        characterPrefix chi (i + 1) := by
    apply mul_nonneg _ (prefix_nonneg chi hc hcert _)
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < i by
      have := (mem_Ico.mp hi).1; omega))
      (by norm_num) (by linarith)
  have hab := Finset.sum_Ico_by_parts
    (fun k : ℕ => (k : ℝ) ^ (-sigma)) (fun k : ℕ => (chi k).re)
    (show 1 < n by omega)
  simp only [smul_eq_mul, Nat.cast_one] at hab
  change (∑ k ∈ Ico 1 n, (k : ℝ) ^ (-sigma) * (chi k).re) =
    ((n - 1 : ℕ) : ℝ) ^ (-sigma) * characterPrefix chi n -
      (1 : ℝ) ^ (-sigma) * characterPrefix chi 1 -
      ∑ i ∈ Ico 1 (n - 1),
        (((i + 1 : ℕ) : ℝ) ^ (-sigma) - (i : ℝ) ^ (-sigma)) *
          characterPrefix chi (i + 1) at hab
  rw [hp1, mul_zero, sub_zero] at hab
  have hsum :
      1 - (2 : ℝ) ^ (-sigma) ≤
        ∑ i ∈ Ico 1 (n - 1),
          ((i : ℝ) ^ (-sigma) - (i + 1 : ℝ) ^ (-sigma)) * characterPrefix chi (i + 1) := by
    have h := Finset.single_le_sum hdiff (show 1 ∈ Ico 1 (n - 1) by
      simp only [mem_Ico]; omega)
    simpa only [Nat.cast_one, Real.one_rpow, Nat.reduceAdd, hp2, mul_one,
      show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hend : 0 ≤ ((n - 1 : ℕ) : ℝ) ^ (-sigma) * characterPrefix chi n :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (prefix_nonneg chi hc hcert _)
  have he : (∑ k ∈ Ico 1 n, (k : ℝ) ^ (-sigma) * (chi k).re) =
      ∑ k ∈ range n, (k : ℝ) ^ (-sigma) * (chi k).re := by
    rw [sum_Ico_eq_sub _ (by omega)]
    simp [hzero]
  rw [he] at hab
  have hneg :
      (∑ i ∈ Ico 1 (n - 1),
        (((i + 1 : ℕ) : ℝ) ^ (-sigma) - (i : ℝ) ^ (-sigma)) *
          characterPrefix chi (i + 1)) =
      -(∑ i ∈ Ico 1 (n - 1),
        ((i : ℝ) ^ (-sigma) - (i + 1 : ℝ) ^ (-sigma)) * characterPrefix chi (i + 1)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hneg] at hab
  linarith

theorem LFunction_re_lower_of_periodPrefix (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hcert : PeriodPrefixNonnegative chi)
    {sigma : ℝ} (hs : 0 < sigma) :
    1 - (2 : ℝ) ^ (-sigma) ≤ (chi.LFunction (sigma : ℂ)).re := by
  have hlim := tendsto_sum_range_orderedValueSeries chi hc (sigma : ℂ) hs
  rw [orderedValueSeries_eq_LFunction_of_re_pos] at hlim
  have he (k : ℕ) :
      (cpowWeight (sigma : ℂ) k * chi k).re =
        (k : ℝ) ^ (-sigma) * (chi k).re := by
    rw [cpowWeight, show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by simp,
      ← Complex.ofReal_cpow (Nat.cast_nonneg k)]
    simp
  have hl := Complex.continuous_re.continuousAt.tendsto.comp hlim
  simp only [Function.comp_def, Complex.re_sum, he] at hl
  apply ge_of_tendsto hl
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  exact real_partialSum_lower chi hc hcert hs hn

theorem LFunction_re_pos_of_periodPrefix (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hcert : PeriodPrefixNonnegative chi)
    {sigma : ℝ} (hs : 0 < sigma) :
    0 < (chi.LFunction (sigma : ℂ)).re := by
  have hpow : (2 : ℝ) ^ (-sigma) < 1 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show -sigma < 0 by linarith)
  exact (sub_pos.mpr hpow).trans_le (LFunction_re_lower_of_periodPrefix chi hc hcert hs)

theorem LFunction_ne_zero_of_periodPrefix (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hcert : PeriodPrefixNonnegative chi)
    {sigma : ℝ} (hs : 0 < sigma) : chi.LFunction (sigma : ℂ) ≠ 0 := by
  intro hz
  have h := LFunction_re_pos_of_periodPrefix chi hc hcert hs
  simp only [hz, Complex.zero_re, lt_self_iff_false] at h

end LiuWang.Proof.SmallConductorExclusion
