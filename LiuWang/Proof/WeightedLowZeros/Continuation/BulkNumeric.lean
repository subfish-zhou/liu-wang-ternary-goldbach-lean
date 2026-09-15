import LiuWang.Proof.WeightedLowZeros.Continuation.CountBudget

/-! # A paid 6e-10/L bound for the actual source bulk, at exp(3100) -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem bulk_weight_le_exp {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    weight N (bulkCap N) ≤
      1.02 * Real.exp (-0.478 * sourceL N / Real.log (lowScale N)) := by
  have hlog : 25 ≤ Real.log (lowScale N) :=
    (log_scale_bounds (sourceL_ge_3100 hN)).1
  have hgap : 0.478 / Real.log (lowScale N) ≤ 1/51 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hb : 50/51 ≤ bulkCap N := by dsimp [bulkCap]; linarith
  have hp : 0 < bulkCap N := by linarith
  have hratio : (1 - (0.001 : ℝ) ^ bulkCap N) / bulkCap N ≤ 1.02 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0.001) (bulkCap N)]
  rw [bulk_weight_exp (nat_pos_of_exp_le hN)]
  exact mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le

theorem bulk_mother_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a : ℝ} (ha : 0 < a) :
    weight N (bulkCap N) * countMother q (omegaCutoff N q) a ≤ 6e-10 / sourceL N := by
  let L := sourceL N
  have hL : 3100 ≤ L := sourceL_ge_3100 hN
  have hp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hy := omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  have hdecay := source_decay_power hL
  have hw := bulk_weight_le_exp hN
  have hc := countMother_low_uniform hN hq a
  have hc0 := countMother_nonneg q hy.le ha
  have hstep : weight N (bulkCap N) * countMother q (omegaCutoff N q) a ≤
      (1.02 * (4e-26 * (3100 / L)^5)) * (6.5 * L^3 * Real.log (L^3)) := by
    apply mul_le_mul
      (hw.trans (mul_le_mul_of_nonneg_left hdecay (by norm_num))) hc hc0 (by positivity)
  apply hstep.trans
  let K : ℝ := 1.02 * 4e-26 * 3100^5 * 19.5
  have hk : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ = K * (Real.log L / L) / L := by
      rw [Real.log_pow]
      dsimp [K]
      field_simp
      ring
    _ ≤ K * (8.04 / 3100) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (log_over_self_bound hL) hk) hp.le
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num [K]) hp.le

theorem source_bulk_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    bulkSum N q (omegaCutoff N q) (bulkCap N) ≤ 6e-10 / sourceL N := by
  have hy := omegaCutoff_pos (exp_2000_le_of_exp_3100_le hN) (NeZero.pos q)
  have hb : 0 < bulkCap N := by linarith [(bulkCap_bounds hN hq).1]
  exact (bulkSum_le (source_endpoint_ge_thousand hN) hy.le (by norm_num : (0 : ℝ) < 1) hb).trans
    (bulk_mother_numeric hN hq (by norm_num))

theorem lowSum_numeric_bulk_and_actual_tail {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    lowSum N q ≤ 6e-10 / sourceL N + tailSum N q (omegaCutoff N q) (bulkCap N) := by
  change (∑ chi : Character q, weightedSum N chi (omegaCutoff N q)) ≤ _
  rw [sum_split_at N q (omegaCutoff N q) (bulkCap N)]
  exact add_le_add (source_bulk_numeric hN hq) le_rfl

theorem source_bulk_Jrho_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    (∑ chi : Character q,
      ∑ rho ∈ (CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
        (fun rho => rho.re ≤ bulkCap N),
          (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
            (N : ℝ) * (6e-10 / sourceL N) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => subset_Jrho_le (nat_pos_of_exp_le hN) chi (omegaCutoff N q) eta
      ((CompleteExpansion.zeroValues chi (omegaCutoff N q)).filter
        (fun rho => rho.re ≤ bulkCap N)) (Finset.filter_subset _ _))
  rw [← Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left (source_bulk_numeric hN hq) (Nat.cast_nonneg _))

end LiuWang.Proof.WeightedLowZeros.Continuation
