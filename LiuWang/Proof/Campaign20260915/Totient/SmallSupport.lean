import LiuWang.Proof.Campaign20260915.Totient.PrimeSupport
import LiuWang.Proof.Campaign20260915.Totient.Cutoff
import LiuWang.Proof.Campaign20260915.Totient.M6

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

theorem four_le_nu {x : ℝ} (hx : 3 ≤ x) : 4 ≤ nu x := by
  have hg : (13 / 8 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
    apply le_trans _ (Real.exp_le_exp.mpr Real.one_half_lt_eulerMascheroniConstant.le)
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 3)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hu := loglog_pos_of_three_le hx
  have he := mul_le_mul_of_nonneg_right hg hu.le
  unfold nu
  apply (mul_le_mul_iff_right₀ hu).mp
  field_simp
  nlinarith [sq_nonneg (Real.log (Real.log x) - 16 / 13),
    mul_le_mul_of_nonneg_right he hu.le]

theorem totient_ratio_le_fifteen_fourths_of_small_support {q : ℕ}
    (hq : 0 < q) (hs : q.primeFactors.card ≤ 3) :
    (q : ℝ) / (q.totient : ℝ) ≤ 15 / 4 := by
  apply (totient_ratio_le_first_primes hq).trans
  generalize q.primeFactors.card = k at *
  interval_cases k <;>
    norm_num [Fin.prod_univ_succ, Nat.nth_prime_zero_eq_two,
      Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

theorem totient_ratio_le_nu_of_small_support {q : ℕ}
    (hq : 3 ≤ q) (hs : q.primeFactors.card ≤ 3) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu q :=
  (totient_ratio_le_fifteen_fourths_of_small_support (by omega) hs).trans
    ((by norm_num : (15 / 4 : ℝ) ≤ 4).trans (four_le_nu (by exact_mod_cast hq)))

theorem second_arc_totient_input_of_small_support {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hs : q.primeFactors.card ≤ 3) :
    (q : ℝ) / (q.totient : ℝ) ≤
      LiuWang.Proof.SourceRoute.SecondArc.Continuation.sourceNu (sourceP N) :=
  (totient_ratio_le_fifteen_fourths_of_small_support (NeZero.pos q) hs).trans
    ((by norm_num : (15 / 4 : ℝ) ≤ 4).trans
      (four_le_nu (by linarith [sourceP_ge_ten_billion hN])))

theorem equation_5_44_of_small_support {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) (hs : q.primeFactors.card ≤ 3) :
    LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.sourceM6 N q ≤
      (6 / 1000000000 : ℝ) * (N : ℝ) / sourceL N := by
  apply equation_5_44_with_monotonicity_paid hN hq hq1
  have hq3 : (3 : ℝ) ≤ q := by linarith [sourceP_ge_ten_billion hN]
  exact totient_ratio_le_nu_of_small_support (by exact_mod_cast hq3) hs

end LiuWang.Proof.Campaign20260915.Totient
