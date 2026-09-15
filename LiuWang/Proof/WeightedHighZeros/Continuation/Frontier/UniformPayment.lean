import LiuWang.Proof.WeightedHighZeros.Continuation.Frontier.Uniform

/-! # An eighty-fold reciprocal-budget improvement on the original full domain -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

theorem omega_coverIndex_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (coverIndex (omegaCutoff N q) (sourceT N) 2 : ℝ) ≤
      30 * Real.log (sourceL N) + 1 := by
  have hu : 1 ≤ omegaCutoff N q := by
    linarith [Parameters.omegaCutoff_ge (NeZero.pos q) hq]
  have ht := Parameters.sourceT_pos (Parameters.exp_2000_le_of_exp_3100_le hN)
  have hl := source_log_ge_one hN
  have hlogT : Real.log (sourceT N / omegaCutoff N q) ≤
      15 * Real.log (sourceL N) := by
    rw [Real.log_div ht.ne' (by linarith : omegaCutoff N q ≠ 0), Parameters.log_sourceT]
    linarith [Real.log_nonneg hu]
  have hlog2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hquot : Real.log (sourceT N / omegaCutoff N q) / Real.log 2 ≤
      30 * Real.log (sourceL N) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog2
      (by linarith : 0 ≤ 30 * Real.log (sourceL N))
    linarith
  have hc : (coverIndex (omegaCutoff N q) (sourceT N) 2 : ℝ) ≤
      ⌈30 * Real.log (sourceL N)⌉₊ := by
    exact_mod_cast Nat.ceil_mono hquot
  exact hc.trans (Nat.ceil_lt_add_one (by linarith : 0 ≤ 30 * Real.log (sourceL N))).le

theorem omega_shell_log_le {N q j : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hj : j < coverIndex (omegaCutoff N q) (sourceT N) 2 + 1) :
    Real.log ((q : ℝ) * ((2 : ℝ) ^ (j + 1) * omegaCutoff N q)) ≤
      38 * Real.log (sourceL N) := by
  have hL := source_log_ge_one hN
  have hP := Parameters.sourceP_pos (Parameters.exp_2000_le_of_exp_3100_le hN)
  have hj' : (j : ℝ) + 1 ≤ 30 * Real.log (sourceL N) + 2 := by
    have hh : j ≤ coverIndex (omegaCutoff N q) (sourceT N) 2 := by omega
    have hh' : (j : ℝ) ≤ coverIndex (omegaCutoff N q) (sourceT N) 2 := by exact_mod_cast hh
    linarith [omega_coverIndex_le hN hq]
  have he : (q : ℝ) * ((2 : ℝ) ^ (j + 1) * omegaCutoff N q) =
      (2 : ℝ) ^ (j + 1) * (3.36 * sourceP N) := by
    unfold omegaCutoff
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne q)]
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) hP.ne', Real.log_pow, Parameters.log_sourceP]
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog336 : Real.log 3.36 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3.36)]
  have hm := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ j + 1)
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

theorem uniformGeometric_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    uniformGeometric q (omegaCutoff N q) (coverIndex (omegaCutoff N q) (sourceT N) 2) ≤
      25000 * q * Real.log (sourceL N) ^ (2 : ℕ) := by
  have hlog := source_log_ge_one hN
  have hu := Parameters.omegaCutoff_ge (NeZero.pos q) hq
  have hterm (j : ℕ)
      (hj : j ∈ Finset.range (coverIndex (omegaCutoff N q) (sourceT N) 2 + 1)) :
      uniformShell q ((2 : ℝ) ^ j * omegaCutoff N q)
        ((2 : ℝ) ^ (j + 1) * omegaCutoff N q) ≤
          760 * q * Real.log (sourceL N) := by
    have hlo : 0 < (2 : ℝ) ^ j * omegaCutoff N q := by positivity
    have hy : 4 ≤ (2 : ℝ) ^ (j + 1) * omegaCutoff N q := by
      have hp := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ (10 * q * ((2 : ℝ) ^ (j + 1) * omegaCutoff N q) *
          Real.log ((q : ℝ) * ((2 : ℝ) ^ (j + 1) * omegaCutoff N q))) /
            ((2 : ℝ) ^ j * omegaCutoff N q) :=
        div_le_div_of_nonneg_right (uniform_four_le_ten q hy) hlo.le
      _ = 20 * q * Real.log ((q : ℝ) * ((2 : ℝ) ^ (j + 1) * omegaCutoff N q)) := by
        rw [pow_succ]
        field_simp
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (omega_shell_log_le hN hq (Finset.mem_range.mp hj))
          (by positivity : 0 ≤ 20 * (q : ℝ))
        linarith
  have hc : (coverIndex (omegaCutoff N q) (sourceT N) 2 : ℝ) + 1 ≤
      32 * Real.log (sourceL N) := by linarith [omega_coverIndex_le hN hq]
  have hs := Finset.sum_le_sum hterm
  have hm := mul_le_mul_of_nonneg_right hc
    (by positivity : 0 ≤ 760 * q * Real.log (sourceL N))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at hs
  have hh : uniformGeometric q (omegaCutoff N q)
      (coverIndex (omegaCutoff N q) (sourceT N) 2) ≤
        24320 * q * Real.log (sourceL N) ^ (2 : ℕ) :=
    hs.trans (hm.trans_eq (by ring))
  have hn : 0 ≤ (q : ℝ) * Real.log (sourceL N) ^ (2 : ℕ) := by positivity
  nlinarith

theorem uniformReciprocal_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    uniformReciprocal N q ≤ 25000 * q * Real.log (sourceL N) ^ (2 : ℕ) :=
  (min_le_right _ _).trans (uniformGeometric_paid hN hq)

theorem actual_reciprocal_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    bandSum 1 q (omegaCutoff N q) (sourceT N) ≤
      25000 * q * Real.log (sourceL N) ^ (2 : ℕ) :=
  (actual_reciprocal_le_uniform hN).trans (uniformReciprocal_paid hN hq)

theorem frontierCap_paid_uniform {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    frontierCap N q ≤ (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hs := (frontierCap_le_reciprocal N q).trans
    (mul_le_mul_of_nonneg_left (actual_reciprocal_paid hN hq) (by positivity))
  have he : (N : ℝ) ^ (-1 / 50 : ℝ) = Real.exp (-sourceL N / 50) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
    congr 1
    unfold sourceL
    ring
  rw [he] at hs
  have hp := mul_le_mul_of_nonneg_right
    (frontier_scalar_payment (Parameters.sourceL_ge_3100 hN))
      (show 0 ≤ (q : ℝ) / 80 by positivity)
  exact hs.trans (by convert hp using 1 <;> ring)

theorem combined_payment_uniform {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    cappedHighSum N q + (∫ alpha in (19 / 20 : ℝ)..(49 / 50),
      layerKernel N alpha * sourceMass N q alpha) ≤
        (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) := by
  rw [← frontierCap_eq_old_cap_add_middle (Parameters.nat_pos_of_exp_le hN)]
  exact frontierCap_paid_uniform hN hq

theorem original_frontier_uniform_reduction {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    highSum N q ≤ (1 / 800000 : ℝ) * q / sourceL N ^ (4 : ℕ) +
      ∫ alpha in (49 / 50 : ℝ)..1, layerKernel N alpha * sourceMass N q alpha := by
  rw [highSum_eq_frontierCap_add_integral (Parameters.nat_pos_of_exp_le hN)]
  exact add_le_add (frontierCap_paid_uniform hN hq) le_rfl

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
