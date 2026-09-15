import LiuWang.Proof.WeightedHighZeros.LargeLog

/-!
# An original-domain finite reciprocal-height payment

`bandSum 1` is the actual ordinary-L reciprocal sum, not a limiting tail.
The existing finite split and covering theorems retain both closed boundaries.
Only the frozen, proved total-count bound is used.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedHighZeros.Continuation

theorem shellBound_one (q : ℕ) (u y : ℝ) :
    shellBound 1 q u y = countBudget q y / u := by
  simp [shellBound, decay]

theorem log_ten_le_three : Real.log 10 ≤ 3 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (x := 1) (by norm_num)
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
    (show (5 / 2 : ℝ) ≤ Real.exp 1 by norm_num at h; linarith) 3
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  linarith

theorem log_ten_thousand_le : Real.log 10000 ≤ 12 := by
  rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [log_ten_le_three]

theorem source_log_ge_one {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 ≤ Real.log (sourceL N) := by
  exact (Real.le_log_iff_exp_le
    (by linarith [Parameters.sourceL_ge_3100 hN])).mpr
    (Real.exp_one_lt_three.le.trans (by linarith [Parameters.sourceL_ge_3100 hN]))

theorem coverIndex_le_source {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (coverIndex 10000 (sourceT N) 2 : ℝ) ≤ 30 * Real.log (sourceL N) + 1 := by
  have hN' := Parameters.exp_2000_le_of_exp_3100_le hN
  have hT : 10000 ≤ sourceT N := by
    have hp := pow_le_pow_right₀ (Parameters.one_le_sourceL hN')
      (by norm_num : 2 ≤ (15 : ℕ))
    have hL := Parameters.sourceL_ge_3100 hN
    change _ ≤ sourceL N ^ (15 : ℕ)
    nlinarith
  have hratio : 0 ≤ Real.log (sourceT N / 10000) :=
    Real.log_nonneg ((le_div_iff₀ (by norm_num)).mpr (by linarith))
  have hlog2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT : Real.log (sourceT N / 10000) ≤ 15 * Real.log (sourceL N) := by
    rw [Real.log_div (Parameters.sourceT_pos hN').ne' (by norm_num),
      Parameters.log_sourceT]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10000)]
  have hquot : Real.log (sourceT N / 10000) / Real.log 2 ≤
      30 * Real.log (sourceL N) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog2
      (by linarith [source_log_ge_one hN] : 0 ≤ 30 * Real.log (sourceL N))
    linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.log (sourceT N / 10000) /
    Real.log 2 from div_nonneg hratio (by linarith))
  change (⌈Real.log (sourceT N / 10000) / Real.log 2⌉₊ : ℝ) ≤ _
  linarith

theorem shell_log_le_source {N q j : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hj : j < coverIndex 10000 (sourceT N) 2 + 1) :
    Real.log ((q : ℝ) * ((2 : ℝ) ^ (j + 1) * 10000)) ≤
      47 * Real.log (sourceL N) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hqlog := Real.log_le_log hq0 hq
  rw [Parameters.log_sourceP] at hqlog
  have hj' : (j : ℝ) + 1 ≤ 30 * Real.log (sourceL N) + 2 := by
    have hh : j ≤ coverIndex 10000 (sourceT N) 2 := by omega
    have hh' : (j : ℝ) ≤ coverIndex 10000 (sourceT N) 2 := by exact_mod_cast hh
    linarith [coverIndex_le_source hN]
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hlog2 hj0
  rw [Real.log_mul hq0.ne' (by positivity),
    Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith [source_log_ge_one hN, log_ten_thousand_le]

theorem geometric_reciprocal_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    geometricBound 1 q 10000 2 (coverIndex 10000 (sourceT N) 2) ≤
      30080 * q * Real.log (sourceL N) ^ (2 : ℕ) := by
  have hlog := source_log_ge_one hN
  have hterm (j : ℕ) (hj : j ∈ Finset.range (coverIndex 10000 (sourceT N) 2 + 1)) :
      shellBound 1 q ((2 : ℝ) ^ j * 10000) ((2 : ℝ) ^ (j + 1) * 10000) ≤
        940 * q * Real.log (sourceL N) := by
    have hu : 0 < (2 : ℝ) ^ j * 10000 := by positivity
    have hy : 10000 ≤ (2 : ℝ) ^ (j + 1) * 10000 := by
      have hh := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j + 1)
      linarith
    rw [shellBound_one]
    calc
      _ ≤ (10 * q * ((2 : ℝ) ^ (j + 1) * 10000) *
          Real.log ((q : ℝ) * ((2 : ℝ) ^ (j + 1) * 10000))) /
            ((2 : ℝ) ^ j * 10000) :=
        div_le_div_of_nonneg_right (countBudget_le_ten hy) hu.le
      _ = 20 * q * Real.log ((q : ℝ) * ((2 : ℝ) ^ (j + 1) * 10000)) := by
        rw [pow_succ]
        field_simp
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (shell_log_le_source hN hq (Finset.mem_range.mp hj))
          (by positivity : 0 ≤ 20 * (q : ℝ))
        nlinarith
  have hc : (coverIndex 10000 (sourceT N) 2 : ℝ) + 1 ≤
      32 * Real.log (sourceL N) := by linarith [coverIndex_le_source hN]
  have hs := Finset.sum_le_sum hterm
  have hb : 0 ≤ 940 * q * Real.log (sourceL N) := by positivity
  have hm := mul_le_mul_of_nonneg_right hc hb
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at hs
  exact hs.trans (hm.trans_eq (by ring))

theorem actual_reciprocal_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    bandSum 1 q (omegaCutoff N q) (sourceT N) ≤
      2000000 * q * Real.log (sourceL N) ^ (2 : ℕ) := by
  have hu : 1 ≤ omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have hlog := source_log_ge_one hN
  have hlow : bandSum 1 q (omegaCutoff N q) 10000 ≤
      1500000 * q * Real.log (sourceL N) := by
    have hc0 : 0 ≤ countBudget q 10000 :=
      (Nat.cast_nonneg (familyCount q 0 10000)).trans
        (familyCount_le_countBudget q 0 (by norm_num))
    have hqlog := Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos q)) hq
    rw [Parameters.log_sourceP] at hqlog
    have hh := countBudget_le_ten (q := q) (y := 10000) (by norm_num)
    rw [Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne q)) (by norm_num)] at hh
    have hlog' : Real.log q + Real.log 10000 ≤ 15 * Real.log (sourceL N) := by
      linarith [log_ten_thousand_le]
    calc
      _ ≤ shellBound 1 q (omegaCutoff N q) 10000 :=
        bandSum_le_shellBound (by norm_num) hu (by norm_num)
      _ ≤ countBudget q 10000 := by rw [shellBound_one]; exact div_le_self hc0 hu
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hlog' (by positivity : 0 ≤ 100000 * (q : ℝ))
        nlinarith
  have hhigh : bandSum 1 q 10000 (sourceT N) ≤
      30080 * q * Real.log (sourceL N) ^ (2 : ℕ) :=
    ((bandSum_mono_height 1 q 10000
      (height_le_cover (by norm_num)
        (Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN))
        (by norm_num : (1 : ℝ) < 2))).trans
      (bandSum_le_geometricBound (by norm_num) (by norm_num) (by norm_num) _)).trans
      (geometric_reciprocal_le hN hq)
  have hs := (bandSum_split_le 1 q (omegaCutoff N q) 10000 (sourceT N)).trans
    (add_le_add hlow hhigh)
  have hsq : Real.log (sourceL N) ≤ Real.log (sourceL N) ^ (2 : ℕ) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 1500000 * (q : ℝ))
  have hn : 0 ≤ (q : ℝ) * Real.log (sourceL N) ^ (2 : ℕ) := by positivity
  nlinarith

end LiuWang.Proof.WeightedHighZeros.Continuation
