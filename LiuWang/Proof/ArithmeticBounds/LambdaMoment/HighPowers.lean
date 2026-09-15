import LiuWang.Proof.ArithmeticBounds.LambdaMoment.Support
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

/-! 大 N 域上的高素数幂尾项。以收敛的 3/2 幂级数作统一上界，
不枚举素数，也不把尾界作为假设。 -/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.ArithmeticBounds.LambdaMoment

open scoped BigOperators
open Parameters

def exponentsFor (N : Nat) (X : Real) (p : Nat) : Finset Nat :=
  (Finset.Icc 1 (exponentCutoff N)).filter
    (fun e => sourceVaughanU N < ((p ^ e : Nat) : Real) ∧
      ((p ^ e : Nat) : Real) ≤ X)

def W1 (N : Nat) (X : Real) : Real :=
  ∑ p ∈ primeBases N,
    if sourceVaughanU N < (p : Real) ∧ (p : Real) ≤ X
    then Real.log p ^ 2 / p else 0

def W2 (N : Nat) (X : Real) : Real :=
  ∑ p ∈ primeBases N, ∑ e ∈ (exponentsFor N X p).filter (2 ≤ ·),
    Real.log p ^ 2 / (p : Real) ^ e

def W3 (N : Nat) (X : Real) : Real :=
  ∑ p ∈ primeBases N, ∑ f ∈ exponentsFor N X p,
    ∑ _e ∈ (exponentsFor N X p).filter (· < f),
      Real.log p ^ 2 / (p : Real) ^ f

theorem exponentsFor_card_le (N p : Nat) (X : Real) :
    (exponentsFor N X p).card ≤ exponentCutoff N := by
  calc
    _ ≤ (Finset.Icc 1 (exponentCutoff N)).card := Finset.card_filter_le _ _
    _ = _ := by simp

theorem prime_rpow_sum_le_three (N : Nat) :
    (∑ p ∈ primeBases N, (p : Real) ^ (-(3 / 2 : Real))) ≤ 3 := by
  calc
    _ ≤ ∑' p : Nat, (p : Real) ^ (-(3 / 2 : Real)) :=
      (Real.summable_nat_rpow.mpr (by norm_num)).sum_le_tsum _
        (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ 3 := by
      convert AnalyticNumberTheory.LargeSieve.tsum_nat_rpow_neg_le
        (3 / 2) (by norm_num)
        using 1
      norm_num

theorem high_power_term_le {N p e : Nat}
    (hN : Real.exp 2000 ≤ (N : Real)) (hp : p.Prime) (hpN : p ≤ N)
    (he : 2 ≤ e) (hU : sourceVaughanU N < ((p ^ e : Nat) : Real)) :
    Real.log p ^ 2 / (p : Real) ^ e ≤
      (Interfaces.sourceL N ^ 2 * Real.exp (-Real.log (sourceVaughanU N) / 4)) *
        (p : Real) ^ (-(3 / 2 : Real)) := by
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlN : Real.log p ≤ Interfaces.sourceL N :=
    Real.log_le_log hp0 (by exact_mod_cast hpN)
  have hlU := Real.log_lt_log (sourceVaughanU_pos hN) hU
  rw [Nat.cast_pow, Real.log_pow] at hlU
  have he' : (2 : Real) ≤ e := by exact_mod_cast he
  have hexp : -(e : Real) * Real.log p ≤
      -Real.log (sourceVaughanU N) / 4 + Real.log p * (-(3 / 2 : Real)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 he') hlp]
  have hfactor : ((p : Real) ^ e)⁻¹ ≤
      Real.exp (-Real.log (sourceVaughanU N) / 4) *
        (p : Real) ^ (-(3 / 2 : Real)) := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_add,
      ← Real.exp_log (pow_pos hp0 e), ← Real.exp_neg, Real.log_pow]
    exact Real.exp_le_exp.2 (by simpa only [neg_mul] using hexp)
  calc
    _ = Real.log p ^ 2 * ((p : Real) ^ e)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ Interfaces.sourceL N ^ 2 *
        (Real.exp (-Real.log (sourceVaughanU N) / 4) *
          (p : Real) ^ (-(3 / 2 : Real))) :=
      mul_le_mul (pow_le_pow_left₀ hlp hlN 2) hfactor (by positivity) (sq_nonneg _)
    _ = _ := by ring

theorem W2_le_cutoff {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    W2 N X ≤ 3 * (exponentCutoff N : Real) * Interfaces.sourceL N ^ 2 *
      Real.exp (-Real.log (sourceVaughanU N) / 4) := by
  let A := Interfaces.sourceL N ^ 2 * Real.exp (-Real.log (sourceVaughanU N) / 4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ p ∈ primeBases N,
        (exponentCutoff N : Real) * (A * (p : Real) ^ (-(3 / 2 : Real))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpm := Finset.mem_filter.1 hp
      calc
        _ ≤ ∑ _e ∈ (exponentsFor N X p).filter (2 ≤ ·),
            A * (p : Real) ^ (-(3 / 2 : Real)) := by
          apply Finset.sum_le_sum
          intro e he
          have hem := Finset.mem_filter.1 he
          exact high_power_term_le hN hpm.2 (Finset.mem_Icc.1 hpm.1).2 hem.2
            (Finset.mem_filter.1 hem.1).2.1
        _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg p) _))
          exact_mod_cast (Finset.card_filter_le _ _).trans (exponentsFor_card_le N p X)
    _ = (exponentCutoff N : Real) * A *
        (∑ p ∈ primeBases N, (p : Real) ^ (-(3 / 2 : Real))) := by
      simp only [mul_assoc, Finset.mul_sum]
    _ ≤ (exponentCutoff N : Real) * A * 3 :=
      mul_le_mul_of_nonneg_left (prime_rpow_sum_le_three N) (by positivity)
    _ = _ := by dsimp [A]; ring

theorem W3_le_cutoff {N : Nat} {X : Real}
    (hN : Real.exp 2000 ≤ (N : Real)) :
    W3 N X ≤ 3 * (exponentCutoff N : Real) ^ 2 * Interfaces.sourceL N ^ 2 *
      Real.exp (-Real.log (sourceVaughanU N) / 4) := by
  let A := Interfaces.sourceL N ^ 2 * Real.exp (-Real.log (sourceVaughanU N) / 4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ p ∈ primeBases N,
        (exponentCutoff N : Real) ^ 2 * (A * (p : Real) ^ (-(3 / 2 : Real))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpm := Finset.mem_filter.1 hp
      calc
        _ ≤ ∑ _f ∈ exponentsFor N X p,
            (exponentCutoff N : Real) * (A * (p : Real) ^ (-(3 / 2 : Real))) := by
          apply Finset.sum_le_sum
          intro f hf
          calc
            _ ≤ ∑ _e ∈ (exponentsFor N X p).filter (· < f),
                A * (p : Real) ^ (-(3 / 2 : Real)) := by
              apply Finset.sum_le_sum
              intro e he
              have hem := Finset.mem_filter.1 he
              have he1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hem.1).1).1
              exact high_power_term_le hN hpm.2 (Finset.mem_Icc.1 hpm.1).2
                (by omega) (Finset.mem_filter.1 hf).2.1
            _ ≤ _ := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast (Finset.card_filter_le _ _).trans (exponentsFor_card_le N p X)
        _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, pow_two, mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast exponentsFor_card_le N p X
    _ = (exponentCutoff N : Real) ^ 2 * A *
        (∑ p ∈ primeBases N, (p : Real) ^ (-(3 / 2 : Real))) := by
      simp only [mul_assoc, Finset.mul_sum]
    _ ≤ (exponentCutoff N : Real) ^ 2 * A * 3 :=
      mul_le_mul_of_nonneg_left (prime_rpow_sum_le_three N) (by positivity)
    _ = _ := by dsimp [A]; ring

theorem log_U_ge_third_L {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) :
    Interfaces.sourceL N / 3 ≤ Real.log (sourceVaughanU N) := by
  rw [log_sourceVaughanU hN]
  have := nat_mul_log_lt (sourceL_ge_2000 hN) (k := 16) (by norm_num)
  norm_num only [Nat.cast_ofNat] at this
  nlinarith [sourceL_pos hN]

theorem pow_eight_le_exp_twelfth {L : Real} (hL : 3100 ≤ L) :
    L ^ 8 ≤ Real.exp (L / 12) := by
  have hL0 : 0 ≤ L := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (x := L / 192) (by positivity)
  have he : L / 25 ≤ Real.exp (L / 192) := by
    nlinarith [mul_nonneg hL0 (show 0 ≤ L - 3100 by linarith)]
  have he2 := pow_le_pow_left₀ (by positivity : 0 ≤ L / 25) he 2
  rw [← Real.exp_nat_mul] at he2
  have hex : L ≤ Real.exp (L / 96) := by
    norm_num only [Nat.cast_ofNat] at he2
    rw [show (2 : Real) * (L / 192) = L / 96 by ring] at he2
    nlinarith [mul_nonneg hL0 (show 0 ≤ L - 3100 by linarith)]
  have he8 := pow_le_pow_left₀ hL0 hex 8
  rw [← Real.exp_nat_mul] at he8
  norm_num only [Nat.cast_ofNat] at he8
  rwa [show (8 : Real) * (L / 96) = L / 12 by ring] at he8

theorem cutoff_tail_le_681 {N : Nat} (hN : Real.exp 3100 ≤ (N : Real)) :
    3 * (exponentCutoff N : Real) ^ 2 * Interfaces.sourceL N ^ 2 *
      Real.exp (-Real.log (sourceVaughanU N) / 4) ≤ 681 / 10000 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_ge_3100 hN
  have hL0 := sourceL_pos hn
  have hK : (exponentCutoff N : Real) ≤ 2 * Interfaces.sourceL N :=
    Nat.floor_le (by positivity)
  have hdec : Real.exp (-Real.log (sourceVaughanU N) / 4) ≤
      (Real.exp (Interfaces.sourceL N / 12))⁻¹ := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.2
    linarith [log_U_ge_third_L hn]
  calc
    _ ≤ 12 * Interfaces.sourceL N ^ 4 *
        (Real.exp (Interfaces.sourceL N / 12))⁻¹ := by
      calc
        _ ≤ 3 * (2 * Interfaces.sourceL N) ^ 2 * Interfaces.sourceL N ^ 2 *
            (Real.exp (Interfaces.sourceL N / 12))⁻¹ := by gcongr
        _ = _ := by ring
    _ ≤ 12 * Interfaces.sourceL N ^ 4 * (Interfaces.sourceL N ^ 8)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (inv_le_inv₀ (Real.exp_pos _) (pow_pos hL0 _)).2 (pow_eight_le_exp_twelfth hL)
    _ = 12 / Interfaces.sourceL N ^ 4 := by field_simp
    _ ≤ 681 / 10000 := by
      apply (div_le_iff₀ (pow_pos hL0 4)).2
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 3100) hL 4
      norm_num at hpow
      linarith

theorem W2_le_681 {N : Nat} {X : Real}
    (hN : Real.exp 3100 ≤ (N : Real)) : W2 N X ≤ 681 / 10000 := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hK : (exponentCutoff N : Real) ≤ (exponentCutoff N : Real) ^ 2 := by
    have : 1 ≤ exponentCutoff N := by
      apply (Nat.le_floor_iff (mul_nonneg (by norm_num) (sourceL_pos hn).le)).2
      have := sourceL_ge_3100 hN
      norm_num
      linarith
    have : (1 : Real) ≤ exponentCutoff N := by exact_mod_cast this
    nlinarith
  calc
    _ ≤ 3 * (exponentCutoff N : Real) ^ 2 * Interfaces.sourceL N ^ 2 *
        Real.exp (-Real.log (sourceVaughanU N) / 4) :=
      (W2_le_cutoff hn).trans (by gcongr)
    _ ≤ 681 / 10000 := cutoff_tail_le_681 hN

theorem W2_le_25876 {N : Nat} {X : Real}
    (hN : Real.exp 3100 ≤ (N : Real)) : W2 N X ≤ 25876 / 10000 :=
  (W2_le_681 hN).trans (by norm_num)

theorem W3_le_681 {N : Nat} {X : Real}
    (hN : Real.exp 3100 ≤ (N : Real)) : W3 N X ≤ 681 / 10000 :=
  (W3_le_cutoff (exp_2000_le_of_exp_3100_le hN)).trans (cutoff_tail_le_681 hN)

end LiuWang.Proof.ArithmeticBounds.LambdaMoment
