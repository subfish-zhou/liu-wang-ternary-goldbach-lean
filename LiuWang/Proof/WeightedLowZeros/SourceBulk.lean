import LiuWang.Proof.WeightedLowZeros.Density
import LiuWang.Proof.WeightedLowZeros.Exceptional

/-! # The source's 0.478 real-part split, without an unpaid density premise -/

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedLowZeros

def bulkCap (N : ℕ) : ℝ := 1 - 0.478 / Real.log (lowScale N)

theorem bulkCap_bounds {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    1 / 2 ≤ bulkCap N ∧ bulkCap N < 1 := by
  have hx := (lowScale_parameters hN hq).1
  have hl : 1 < Real.log (lowScale N) := by
    apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
    linarith [Real.exp_one_lt_d9]
  have hp : 0 < 0.478 / Real.log (lowScale N) := by positivity
  have hu : 0.478 / Real.log (lowScale N) ≤ 0.478 :=
    div_le_self (by norm_num) hl.le
  dsimp [bulkCap]
  constructor <;> linarith

theorem weight_exp_form {N : ℕ} (hN : 0 < N) (beta : ℝ) :
    weight N beta = (1 - (0.001 : ℝ) ^ beta) / beta *
      Real.exp ((beta - 1) * sourceL N) := by
  rw [weight, Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)]
  congr 2
  exact mul_comm _ _

theorem bulk_weight_exp {N : ℕ} (hN : 0 < N) :
    weight N (bulkCap N) = (1 - (0.001 : ℝ) ^ bulkCap N) / bulkCap N *
      Real.exp (-0.478 * sourceL N / Real.log (lowScale N)) := by
  rw [weight_exp_form hN]
  congr 2
  unfold bulkCap
  ring

theorem source_bulk_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a : ℝ} (ha : 0 < a) :
    bulkSum N q (omegaCutoff N q) (bulkCap N) ≤
      ((1 - (0.001 : ℝ) ^ bulkCap N) / bulkCap N *
        Real.exp (-0.478 * sourceL N / Real.log (lowScale N))) *
          countMother q (omegaCutoff N q) a := by
  have h := bulkSum_le (q := q) (source_endpoint_ge_thousand hN)
    (le_trans (by norm_num) (Parameters.omegaCutoff_ge (NeZero.pos q) hq)) ha
    (by linarith [(bulkCap_bounds hN hq).1] : 0 < bulkCap N)
  rwa [bulk_weight_exp (Parameters.nat_pos_of_exp_le hN)] at h

theorem source_two_level {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {a : ℝ} (ha : 0 < a) :
    lowSum N q ≤ weight N (bulkCap N) * countMother q (omegaCutoff N q) a +
      (0.999 - weight N (bulkCap N)) * familyCount q (bulkCap N) (omegaCutoff N q) :=
  lowSum_two_level hN hq ha (bulkCap_bounds hN hq).1 (bulkCap_bounds hN hq).2.le

end LiuWang.Proof.WeightedLowZeros
