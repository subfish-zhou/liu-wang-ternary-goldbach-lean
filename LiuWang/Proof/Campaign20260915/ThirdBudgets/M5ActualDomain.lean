import LiuWang.Proof.Campaign20260915.ThirdDomainTail.SourceGate
import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5Scalar

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

def legalHeight (q : ℕ) (y : ℝ) : ℝ :=
  max y (max (100000 / (q : ℝ)) (10000 * Real.log q))

theorem m5_product_lower {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y : ℝ} (hy : middleHeight N q ≤ y) :
    Real.log (10 * Real.pi * sourceL N ^ 7) ≤ Real.log ((q : ℝ) * y) := by
  have hL0 := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  apply Real.log_le_log (by positivity)
  have h := mul_le_mul_of_nonneg_left hy hq0.le
  unfold middleHeight at h
  field_simp at h
  exact h

theorem m5_log_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {y : ℝ} (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N)) :
    1 ≤ y ∧ 59.4 ≤ Real.log ((q : ℝ) * y) ∧
      Real.log ((q : ℝ) * y) ≤ 21 * Real.log (sourceL N) ∧
      180 ≤ 4 * Real.log ((q : ℝ) * y) - Real.log q := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hlow := (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1.trans hy.1
  have hy0 := lowHeight_pos.trans_le hlow
  have hlogL : 8 ≤ Real.log (sourceL N) :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hlo := m5_product_lower hN hy.1
  rw [Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0)
    (pow_pos hL0 7).ne', Real.log_pow] at hlo
  simp only [Nat.cast_ofNat] at hlo
  have hqlog := Real.log_le_log hq0 hq1
  rw [sourceP1, Real.log_pow] at hqlog
  simp only [Nat.cast_ofNat] at hqlog
  have hup := Real.log_le_log hy0 hy.2
  rw [sourceT, Real.log_pow] at hup
  simp only [Nat.cast_ofNat] at hup
  refine ⟨lowHeight_ge_one.trans hlow, ?_, ?_, ?_⟩
  · linarith [M6Certificate.log_ten_pi_bounds.1]
  · rw [Real.log_mul hq0.ne' hy0.ne']
    linarith
  · linarith [M6Certificate.log_ten_pi_bounds.1]

theorem m5_legal_height_domain {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    {y : ℝ} (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N)) :
    y ≤ legalHeight q y ∧
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ legalHeight q y ∧
      legalHeight q y ≤ sourceT N ∧ 1 ≤ legalHeight q y ∧
      36 ≤ Real.log ((q : ℝ) * legalHeight q y) ∧
      Real.log ((q : ℝ) * legalHeight q y) ≤
        (11 / 10) * Real.log ((q : ℝ) * y) ∧
      4 * Real.log ((q : ℝ) * legalHeight q y) ≤ sourceL N / 4 := by
  have hd := m5_log_domain hN hq1 hy
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy0 : 0 < y := by linarith [hd.1]
  have hyle : y ≤ legalHeight q y := le_max_left _ _
  have hgle : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ legalHeight q y :=
    le_max_right _ _
  have htop : legalHeight q y ≤ sourceT N :=
    max_le hy.2 (high_endpoint_source_domain hN hq1)
  have hlog := Real.log_le_log (mul_pos hq0 hy0)
    (mul_le_mul_of_nonneg_left hyle hq0.le)
  have hratio : Real.log ((q : ℝ) * legalHeight q y) ≤
      (11 / 10) * Real.log ((q : ℝ) * y) := by
    have hg := enlarged_height_source_domain hN hq hq1
    have heg : max (100000 / (q : ℝ)) (10000 * Real.log q) =
        10000 * Real.log q := le_antisymm hg.2 (le_max_right _ _)
    unfold legalHeight
    rw [heg]
    by_cases h : 10000 * Real.log (q : ℝ) ≤ y
    · rw [max_eq_left h]
      linarith [hd.2.1]
    · rw [max_eq_right (le_of_not_ge h)]
      have hlow := (original_height_order (exp_2000_le_of_exp_3100_le hN) hq1).1.trans hy.1
      have hs := Real.log_le_log (mul_pos hq0 lowHeight_pos)
        (mul_le_mul_of_nonneg_left hlow hq0.le)
      exact (M3_density_logs hN hq hq1).2.2.1.trans
        (mul_le_mul_of_nonneg_left hs (by norm_num))
  refine ⟨hyle, hgle, htop, hd.1.trans hyle, by linarith [hd.2.1], hratio, ?_⟩
  have hh := m5_log_domain hN hq1 ⟨hy.1.trans hyle, htop⟩
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hl := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
  linarith [hh.2.2.1]

theorem m5_cutoff_le_legal {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {y : ℝ} (hy : y ∈ Set.Icc (middleHeight N q) (sourceT N)) :
    sourceCutoff q 0.478 y ≤ sourceCutoff q 0.478 (legalHeight q y) := by
  have hd := m5_log_domain hN hq1 hy
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl := Real.log_le_log (mul_pos hq0 (by linarith [hd.1]))
    (mul_le_mul_of_nonneg_left (show y ≤ legalHeight q y from le_max_left _ _) hq0.le)
  exact sub_le_sub_left
    (div_le_div_of_nonneg_left (by norm_num) (by linarith [hd.2.1]) hl) 1

end LiuWang.Proof.Campaign20260915.ThirdBudgets
