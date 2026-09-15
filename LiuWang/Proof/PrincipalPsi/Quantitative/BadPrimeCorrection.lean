import LiuWang.Proof.PrincipalPsi.Quantitative.ZetaFormula
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrincipalLambdaGlobalReduction

/-! # 普通主字符 ψ 的真实坏素数幂修正 -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.NonSymmetricContour
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.PrincipalPsi.Quantitative

theorem principal_psi_eq_coprimePrefix (q : ℕ) (t : ℝ) :
    ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t = coprimeLambdaPrefix ⌊t⌋₊ q := by
  classical
  rw [ExplicitPerron.psi_eq_sum, coprimeLambdaPrefix, Finset.sum_filter]
  have hterm (n : ℕ) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ q) n =
        if n.Coprime q then lambdaNatCoeff n else 0 := by
    by_cases hn : n.Coprime q
    · rw [if_pos hn, MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn), mul_one]
      rfl
    · rw [if_neg hn, MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn), mul_zero]
  simp_rw [hterm]
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr (by have hh := (Finset.mem_Icc.mp hn).2; omega)
  · intro n hn hn'
    have hn0 : n = 0 := by
      have hh := Finset.mem_range.mp hn
      have hh' : ¬ (1 ≤ n ∧ n ≤ ⌊t⌋₊) := by simpa using hn'
      omega
    simp [hn0, lambdaNatCoeff]

theorem principal_psi_add_badMass (q : ℕ) (t : ℝ) :
    ExplicitPerron.psi (1 : DirichletCharacter ℂ 1) t =
      ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t + principalBadLambdaMass ⌊t⌋₊ q := by
  simp only [principal_psi_eq_coprimePrefix]
  exact coprimeLambdaPrefix_one_eq_add_badMass _ _

theorem norm_principal_psi_sub_modulus_one_le {q N : ℕ} (hq : 0 < q) (hN : 2 ≤ N)
    {t : ℝ} (ht : t ≤ (N : ℝ)) :
    ‖ExplicitPerron.psi (1 : DirichletCharacter ℂ q) t -
        ExplicitPerron.psi (1 : DirichletCharacter ℂ 1) t‖ ≤
      (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) := by
  rw [principal_psi_add_badMass q t, sub_add_cancel_left, norm_neg]
  exact norm_principalBadLambdaMass_le_log2 hq (Nat.floor_le_of_le ht) hN

theorem log2_le_twice_log {n : ℕ} (hn : 0 < n) :
    (Nat.log2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hp : ((2 : ℝ) ^ (Nat.log2 n)) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 ^ Nat.log2 n ≤ n by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 hn.ne')
  have hlog := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at hlog
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hh := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (Nat.log2 n) : (0 : ℝ) ≤ _)
  linarith

theorem badMass_cost_source_le {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP1 N) {t : ℝ} (htlo : sourceWindowLower N ≤ t) :
    (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) ≤
      0.000001 * t / sourceT N * sourceL N ^ 2 := by
  have hL1 := one_le_sourceL hN
  have hL0 := sourceL_pos hN
  have hqlog : (Nat.log2 q : ℝ) ≤ sourceL N ^ (6 : ℕ) := by
    apply le_trans _ hq
    exact_mod_cast (show Nat.log2 q ≤ q by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 q)
  have hNlog : (Nat.log2 N + 1 : ℝ) ≤ 3 * sourceL N := by
    have h := log2_le_twice_log (nat_pos_of_exp_le hN)
    change (Nat.log2 N : ℝ) ≤ 2 * sourceL N at h
    linarith
  have hc : (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) ≤
      3 * sourceL N ^ (8 : ℕ) := by
    change _ * sourceL N ≤ _
    calc
      _ ≤ (sourceL N ^ (6 : ℕ)) * (3 * sourceL N) * sourceL N :=
        mul_le_mul_of_nonneg_right (mul_le_mul hqlog hNlog (by positivity) (by positivity)) hL0.le
      _ = _ := by ring
  apply hc.trans
  apply le_trans _ (polynomial_left_cost_source_le hN htlo)
  have hp : sourceL N ^ (8 : ℕ) ≤ sourceL N ^ (45 : ℕ) :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have he : sourceT N ^ 3 = sourceL N ^ (45 : ℕ) := by unfold sourceT; ring
  rw [he]
  nlinarith [pow_nonneg hL0.le 45]

end LiuWang.Proof.PrincipalPsi.Quantitative
