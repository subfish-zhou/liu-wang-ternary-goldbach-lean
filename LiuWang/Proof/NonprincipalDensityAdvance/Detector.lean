import LiuWang.Proof.GlobalZeroDensity.RightLine
import LiuWang.Proof.Interfaces.Main

/-!
# The character-twisted Mobius detector

This is an analytic input toward the nonprincipal sum cited as [C, Theorem]
in Liu--Wang's companion Theorem 7, not a statement of Chen's density bound.
The cutoff and untwisted convolution coefficients are reused, while the
function being detected is the actual ambient character's L-function.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory
open scoped LSeries.notation ArithmeticFunction.zeta
open LiuWang.Proof.Interfaces

namespace LiuWang.Proof.NonprincipalDensityAdvance

def twistedMu {q : ℕ} (chi : Character q) (n : ℕ) : ℂ :=
  chi n * (ArithmeticFunction.moebius n : ℂ)

def Q {q : ℕ} (chi : Character q) (X : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ range ⌈X⌉₊, twistedMu chi n / (n : ℂ) ^ s

def f {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) : ℂ :=
  chi.LFunction s * Q chi X s - 1

def H {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) : ℂ :=
  1 - f chi X s ^ 2

def coefficient {q : ℕ} (chi : Character q) (X : ℝ) (n : ℕ) : ℂ :=
  chi n * GlobalZeroDensity.coefficient X n

theorem coefficient_eq_zero_of_lt {q : ℕ} (chi : Character q) {X : ℝ}
    {n : ℕ} (hn : (n : ℝ) < X) : coefficient chi X n = 0 := by
  rw [coefficient, GlobalZeroDensity.coefficient_eq_zero_of_lt hn, mul_zero]

theorem coefficient_norm_le {q : ℕ} (chi : Character q) {X : ℝ} (hX : 1 < X)
    (n : ℕ) : ‖coefficient chi X n‖ ≤ n.divisors.card := by
  rw [coefficient, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (chi.norm_le_one n)).trans
    (GlobalZeroDensity.coefficient_norm_le hX n)

theorem Q_hasSum {q : ℕ} (chi : Character q) (X : ℝ) (s : ℂ) :
    LSeriesHasSum (fun n => chi n * GlobalZeroDensity.truncatedMu X n) s
      (Q chi X s) := by
  have ht (n : ℕ) :
      LSeries.term (fun n => chi n * GlobalZeroDensity.truncatedMu X n) s n =
        if n ∈ range ⌈X⌉₊ then twistedMu chi n / (n : ℂ) ^ s else 0 := by
    by_cases hn : n = 0
    · subst n
      simp [twistedMu, GlobalZeroDensity.truncatedMu_apply]
    · simp [LSeries.term_of_ne_zero hn, GlobalZeroDensity.truncatedMu_apply,
        Nat.lt_ceil, twistedMu, mul_ite, ite_div]
  change HasSum _ _
  have hz : ∀ n ∉ range ⌈X⌉₊,
      LSeries.term (fun n => chi n * GlobalZeroDensity.truncatedMu X n) s n = 0 :=
    fun n hn => (ht n).trans (if_neg hn)
  have he : Q chi X s = ∑ n ∈ range ⌈X⌉₊,
      LSeries.term (fun n => chi n * GlobalZeroDensity.truncatedMu X n) s n := by
    simp only [Q, ht]
    exact sum_congr rfl (fun n hn => (if_pos hn).symm)
  rw [he]
  exact hasSum_sum_of_ne_finset_zero hz

theorem coefficient_convolution {q : ℕ} (chi : Character q) (X : ℝ) :
    coefficient chi X =
      ((fun n : ℕ => chi n * GlobalZeroDensity.truncatedMu X n) ⍟
        (fun n : ℕ => chi n)) - LSeries.delta := by
  have ht := chi.mul_convolution_distrib
    (GlobalZeroDensity.truncatedMu X) (1 : ℕ → ℂ)
  simp only [mul_one] at ht
  have hb : (GlobalZeroDensity.truncatedMu X : ℕ → ℂ) ⍟ (1 : ℕ → ℂ) =
      ⇑(GlobalZeroDensity.truncatedMu X * (ζ : ArithmeticFunction ℂ)) := by
    rw [LSeries.convolution_one_eq_convolution_zeta]
    have hzeta : (fun n : ℕ => (ζ n : ℂ)) = ⇑(ζ : ArithmeticFunction ℂ) := by
      funext n
      exact (ArithmeticFunction.natCoe_apply (R := ℂ)).symm
    rw [hzeta]
    exact ArithmeticFunction.coe_mul (GlobalZeroDensity.truncatedMu X) (ζ : ArithmeticFunction ℂ)
  rw [hb] at ht
  simp only [Pi.mul_def] at ht
  rw [ht]
  have hd := chi.mul_delta
  simp only [Pi.mul_def] at hd
  rw [← hd]
  ext n
  simp only [coefficient, GlobalZeroDensity.coefficient, Pi.sub_apply, mul_sub,
    ArithmeticFunction.one_apply, LSeries.delta]

theorem f_hasSum {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 1 < s.re) (X : ℝ) :
    LSeriesHasSum (coefficient chi X) s (f chi X s) := by
  have hL : LSeriesHasSum (fun n : ℕ => chi n) s (chi.LFunction s) := by
    rw [chi.LFunction_eq_LSeries hs]
    exact (chi.LSeriesSummable_of_one_lt_re hs).LSeriesHasSum
  have hp := (Q_hasSum chi X s).convolution hL
  rw [coefficient_convolution]
  have hd : LSeriesHasSum LSeries.delta s 1 := by
    change HasSum (fun n => LSeries.term LSeries.delta s n) 1
    simp_rw [LSeries.term_delta]
    exact hasSum_ite_eq (1 : ℕ) (1 : ℂ)
  simpa only [f, mul_comm] using hp.sub hd

theorem differentiable_Q {q : ℕ} (chi : Character q) (X : ℝ) :
    Differentiable ℂ (Q chi X) := by
  apply Differentiable.fun_sum
  intro n _
  by_cases hn : n = 0
  · subst n
    simp [twistedMu]
  · exact (differentiable_const _).div
      (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hn)))
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn)))

theorem differentiable_f {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) : Differentiable ℂ (f chi X) :=
  ((DirichletCharacter.differentiable_LFunction hchi).mul
    (differentiable_Q chi X)).sub_const 1

theorem differentiable_H {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) : Differentiable ℂ (H chi X) :=
  ((differentiable_f hchi X).pow 2).const_sub 1

theorem H_factorization {q : ℕ} [NeZero q] (chi : Character q) (X : ℝ) (s : ℂ) :
    H chi X s = chi.LFunction s *
      (Q chi X s * (2 - chi.LFunction s * Q chi X s)) := by
  unfold H f
  ring

theorem H_eq_zero_of_LFunction_eq_zero {q : ℕ} [NeZero q] {chi : Character q}
    {s : ℂ} (hs : chi.LFunction s = 0) (X : ℝ) : H chi X s = 0 := by
  rw [H_factorization, hs, zero_mul]

theorem analyticOrder_H_ge_LFunction {q : ℕ} [NeZero q] {chi : Character q}
    (hchi : chi ≠ 1) (X : ℝ) (s : ℂ) :
    analyticOrderAt chi.LFunction s ≤ analyticOrderAt (H chi X) s := by
  have hL := (DirichletCharacter.differentiable_LFunction hchi).analyticAt s
  have hQ := (differentiable_Q chi X).analyticAt s
  have he : H chi X = chi.LFunction *
      (fun z => Q chi X z * (2 - chi.LFunction z * Q chi X z)) :=
    funext (H_factorization chi X)
  have ho : AnalyticAt ℂ (fun z => Q chi X z * (2 - chi.LFunction z * Q chi X z)) s :=
    hQ.mul (analyticAt_const.sub (hL.mul hQ))
  rw [he, analyticOrderAt_mul hL ho]
  exact le_self_add

theorem f_eq_moebius_tail {q : ℕ} [NeZero q] (chi : Character q)
    {s : ℂ} (hs : 1 < s.re) (X : ℝ) :
    f chi X s = -chi.LFunction s *
      ∑' n : ℕ, LSeries.term (twistedMu chi) s (n + ⌈X⌉₊) := by
  have hsum : LSeriesSummable (twistedMu chi) s :=
    chi.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hsplit := hsum.sum_add_tsum_nat_add ⌈X⌉₊
  have hQ : (∑ n ∈ range ⌈X⌉₊, LSeries.term (twistedMu chi) s n) = Q chi X s := by
    apply sum_congr rfl
    intro n _
    by_cases hn : n = 0
    · subst n
      simp [twistedMu]
    · exact LSeries.term_of_ne_zero hn _ _
  rw [hQ] at hsplit
  have hinv := DirichletCharacter.LSeries.mul_mu_eq_one chi hs
  rw [← chi.LFunction_eq_LSeries hs] at hinv
  change chi.LFunction s * (∑' n, LSeries.term (twistedMu chi) s n) = 1 at hinv
  rw [← hsplit] at hinv
  unfold f
  rw [← hinv]
  ring

end LiuWang.Proof.NonprincipalDensityAdvance
