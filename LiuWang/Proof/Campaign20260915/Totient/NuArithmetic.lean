import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1.NuDomain

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation
open LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Totient

theorem three_le_nu {x : ℝ} (hx : 3 ≤ x) : 3 ≤ nu x := by
  have hu := loglog_pos_of_three_le hx
  have he := mul_le_mul_of_nonneg_right exp_gamma_ge_one hu.le
  unfold nu
  apply (mul_le_mul_iff_right₀ hu).mp
  field_simp
  nlinarith [sq_nonneg (Real.log (Real.log x) - 3 / 2),
    mul_le_mul_of_nonneg_right he hu.le]

theorem totient_ratio_le_three_of_lt_27 {q : ℕ} (hq : 1 ≤ q) (hq27 : q < 27) :
    (q : ℝ) / (q.totient : ℝ) ≤ 3 := by
  interval_cases q <;>
    norm_num [Nat.totient, Nat.Coprime, Finset.range_add_one,
      Finset.filter_insert, Finset.filter_singleton]

theorem totient_ratio_le_nu_of_three_le_lt_27 {q : ℕ}
    (hq : 3 ≤ q) (hq27 : q < 27) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu q :=
  (totient_ratio_le_three_of_lt_27 (by omega) hq27).trans
    (three_le_nu (by exact_mod_cast hq))

theorem small_totient_ratio_le_nu {x : ℝ} {q : ℕ}
    (hx : 3 ≤ x) (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    (q : ℝ) / (q.totient : ℝ) ≤ nu x := by
  have hnu := two_le_nu hx
  interval_cases q <;> norm_num at * <;> linarith

theorem nu_zero_at_one : nu 1 = 0 := by
  simp [nu]

theorem not_totient_ratio_le_nu_one :
    ¬ (1 : ℝ) / (Nat.totient 1 : ℝ) ≤ nu 1 := by
  norm_num [nu_zero_at_one]

theorem nu_neg_at_two : nu 2 < 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hu : Real.log (Real.log 2) < 0 := Real.log_neg hlog hlog1
  exact add_neg (mul_neg_of_pos_of_neg (Real.exp_pos _) hu)
    (div_neg_of_pos_of_neg (by norm_num) hu)

theorem not_totient_ratio_le_nu_two :
    ¬ (2 : ℝ) / (Nat.totient 2 : ℝ) ≤ nu 2 := by
  norm_num
  linarith [nu_neg_at_two]

end LiuWang.Proof.Campaign20260915.Totient
