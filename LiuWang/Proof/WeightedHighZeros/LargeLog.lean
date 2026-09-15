import LiuWang.Proof.WeightedHighZeros.Consumer

/-!
# A paid high-logarithm subdomain of the original numerical constant

This uses only the frozen R20 region and actual total counts. The larger
threshold is explicit and does not assert the missing `3100 <= log N` range.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros

theorem log_square_budget {L : ℝ} (hL : 100000000 ≤ L) :
    10800 * Real.log L ^ 2 ≤ L := by
  let s := Real.sqrt (L / 100000000)
  have hratio : 1 ≤ L / 100000000 := (le_div_iff₀ (by norm_num)).mpr (by linarith)
  have hs : 1 ≤ s := by
    dsimp [s]
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hratio)
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = L / 100000000 := Real.sq_sqrt (by linarith)
  have hLeq : L = 100000000 * s ^ 2 := by rw [hs2]; ring
  have hbase : Real.log (100000000 : ℝ) ≤ 72 := by
    rw [show (100000000 : ℝ) = 10 ^ (8 : ℕ) by norm_num, Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    norm_num at *
    linarith
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have hlog : Real.log L ≤ 72 * s := by
    rw [hLeq, Real.log_mul (by norm_num) (pow_pos hs0 2).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hsq : Real.log L ^ 2 ≤ (72 * s) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  nlinarith [sq_nonneg s]

theorem source_height_scale {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    heightScale q (sourceT N) = (q : ℝ) * sourceT N := by
  have hL := Parameters.sourceL_ge_3100 hN
  have hT : sourceL N ≤ sourceT N := by
    simpa only [sourceT, pow_one] using
      pow_le_pow_right₀ (by linarith : 1 ≤ sourceL N) (by norm_num : 1 ≤ (15 : ℕ))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  exact max_eq_right (by
    have hh := le_mul_of_one_le_left (by linarith : 0 ≤ sourceT N) hq
    linarith)

theorem source_log_height_upper {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    Real.log (heightScale q (sourceT N)) ≤ 18 * Real.log (sourceL N) := by
  rw [source_height_scale hN, Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne q))
    (Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN)).ne',
    Parameters.log_sourceT]
  have hlogq := Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos q)) hq
  rw [Parameters.log_sourceP] at hlogq
  linarith

theorem decay_le_log_power {N q : ℕ} [NeZero q]
    (hN : Real.exp 100000000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    decay N q (sourceT N) ≤ 1 / sourceL N ^ (30 : ℕ) := by
  have hN' : Real.exp 3100 ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by norm_num)).trans hN
  have hL := Parameters.le_sourceL_of_exp_le hN
  have hlogL : 0 < Real.log (sourceL N) := Real.log_pos (by linarith)
  have hscale : 0 < Real.log (heightScale q (sourceT N)) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hsq := log_square_budget hL
  have hu := source_log_height_upper hN' hq
  have hprod : 30 * Real.log (sourceL N) *
      (20 * Real.log (heightScale q (sourceT N))) ≤ sourceL N := by
    have hm := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 600 * Real.log (sourceL N))
    nlinarith
  have hdiv := (le_div_iff₀ (by positivity : 0 < 20 *
    Real.log (heightScale q (sourceT N)))).mpr hprod
  calc
    decay N q (sourceT N) ≤ Real.exp (-(30 * Real.log (sourceL N))) := by
      apply Real.exp_le_exp.mpr
      change -(sourceL N) / _ ≤ _
      rw [neg_div]
      exact neg_le_neg hdiv
    _ = 1 / sourceL N ^ (30 : ℕ) := by
      rw [Real.exp_neg, show 30 * Real.log (sourceL N) =
        Real.log (sourceL N ^ (30 : ℕ)) by simp only [Real.log_pow, Nat.cast_ofNat],
        Real.exp_log (by positivity)]
      rw [one_div]

theorem countBudget_le_ten {q : ℕ} [NeZero q] {y : ℝ} (hy : 10000 ≤ y) :
    countBudget q y ≤ 10 * q * y * Real.log ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hphi : 1 ≤ q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  have hc : ((q.totient - 1 : ℕ) : ℝ) + 1 = q.totient := by
    exact_mod_cast Nat.sub_add_cancel hphi
  have hB : 0 ≤ 10 * y * Real.log ((q : ℝ) * y) := by
    have := Applications.log_product_ge_eight hq hy
    positivity
  calc
    _ ≤ principalBound y + (q.totient - 1 : ℕ) * nonprincipalBound q y := min_le_left _ _
    _ ≤ 10 * y * Real.log ((q : ℝ) * y) +
        (q.totient - 1 : ℕ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      add_le_add (Applications.principalBound_le_ten (q := q) hy)
        (mul_le_mul_of_nonneg_left (Applications.nonprincipalBound_le_ten hy) (Nat.cast_nonneg _))
    _ = q.totient * (10 * y * Real.log ((q : ℝ) * y)) := by rw [← hc]; ring
    _ ≤ (q : ℝ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le q)) hB
    _ = _ := by ring

theorem highSum_le_large_log {N q : ℕ} [NeZero q]
    (hN : Real.exp 100000000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ 0.0126 * q / sourceL N ^ (4 : ℕ) := by
  have hN' : Real.exp 3100 ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by norm_num)).trans hN
  have hL := Parameters.le_sourceL_of_exp_le hN
  have hL0 : 0 < sourceL N := by linarith
  have hT : sourceL N ≤ sourceT N := by
    simpa only [sourceT, pow_one] using
      pow_le_pow_right₀ (by linarith : 1 ≤ sourceL N) (by norm_num : 1 ≤ (15 : ℕ))
  have hcount0 : 0 ≤ countBudget q (sourceT N) :=
    (Nat.cast_nonneg (familyCount q 0 (sourceT N))).trans
      (familyCount_le_countBudget q 0 (by linarith))
  have hu : 1 ≤ omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hcount : countBudget q (sourceT N) ≤ 180 * q * sourceL N ^ (16 : ℕ) := by
    have hlog := source_log_height_upper hN' hq
    rw [source_height_scale hN'] at hlog
    have hlogL : Real.log (sourceL N) ≤ sourceL N :=
      (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
    calc
      _ ≤ 10 * q * sourceT N * Real.log ((q : ℝ) * sourceT N) :=
        countBudget_le_ten (by linarith)
      _ ≤ 10 * q * sourceT N * (18 * sourceL N) :=
        mul_le_mul_of_nonneg_left (hlog.trans (by linarith))
          (mul_nonneg (by positivity) (by linarith))
      _ = _ := by unfold sourceT; ring
  have hbound : highSum N q ≤ 180 * q / sourceL N ^ (14 : ℕ) := by
    calc
      _ ≤ shellBound N q (omegaCutoff N q) (sourceT N) := highSum_le_single_shell hN' hq
      _ ≤ decay N q (sourceT N) * countBudget q (sourceT N) :=
        div_le_self (mul_nonneg (Real.exp_pos _).le hcount0) hu
      _ ≤ (1 / sourceL N ^ (30 : ℕ)) * (180 * q * sourceL N ^ (16 : ℕ)) :=
        mul_le_mul (decay_le_log_power hN hq) hcount hcount0 (by positivity)
      _ = _ := by field_simp
  have hp : 180 ≤ 0.0126 * sourceL N ^ (10 : ℕ) := by
    have hh : (100 : ℝ) ^ (10 : ℕ) ≤ sourceL N ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith) _
    norm_num at hh
    linarith
  apply hbound.trans
  apply (div_le_div_iff₀ (pow_pos hL0 14) (pow_pos hL0 4)).mpr
  have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (q : ℝ) * sourceL N ^ (4 : ℕ))
  nlinarith [show sourceL N ^ (14 : ℕ) = sourceL N ^ (10 : ℕ) * sourceL N ^ (4 : ℕ) by ring]

theorem primedHighSum_le_large_log {N q : ℕ} [NeZero q]
    (hN : Real.exp 100000000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {exceptional : Option ℂ} (he : ∀ beta, exceptional = some beta → beta.im = 0) :
    primedHighSum N q exceptional ≤ 0.0126 * q / sourceL N ^ (4 : ℕ) := by
  rw [primedHighSum_eq_highSum ((Real.exp_le_exp.mpr (by norm_num)).trans hN) he]
  exact highSum_le_large_log hN hq

end LiuWang.Proof.WeightedHighZeros
