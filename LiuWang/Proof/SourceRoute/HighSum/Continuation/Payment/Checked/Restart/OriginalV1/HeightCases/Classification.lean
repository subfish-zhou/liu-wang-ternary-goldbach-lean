import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.T2Slots
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536.Payment

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.MultiZeroRepulsion
open LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source3536

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases

def ThirdCase (q : ℕ) [NeZero q] (y : ℝ) : Prop :=
  ∀ p : ZeroSlots q 0 y, 0.15 < gap p

theorem actual_height_classification (q : ℕ) [NeZero q] (y : ℝ) :
    FirstCase q y ∨ (¬ FirstCase q y ∧ SecondCase q y) ∨ ThirdCase q y := by
  classical
  by_cases h1 : FirstCase q y
  · exact Or.inl h1
  by_cases h2 : SecondCase q y
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  refine Or.inr (Or.inr ?_)
  intro p
  by_contra h
  have hp : 0.12 < gap p := lt_of_not_ge (fun hp => h1 ⟨p, hp⟩)
  exact h2 ⟨p, hp, le_of_not_gt h⟩

theorem third_closed_count_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y lam : ℝ}
    (hy : omegaCutoff N q ≤ y) (hc : ThirdCase q y) (hlam : lam ≤ 0.15) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y = 0 := by
  have hs : 0 < Real.log ((q : ℝ) * y) := by
    linarith [original_log_product_ge_ten hN hy]
  have : IsEmpty (ClosedSlots q (1 - lam / Real.log ((q : ℝ) * y)) y) := ⟨by
    intro p
    have hp := closedSlot_gap_le hs p
    have hc' := hc (fullSlot p)
    linarith⟩
  rw [← card_closedSlots, Fintype.card_of_isEmpty]

theorem closed_count_le_strict {q : ℕ} [NeZero q] {a b y : ℝ} (hab : a < b) :
    familyCount q b y ≤ strictFamilyCount q a y := by
  apply Finset.sum_le_sum
  intro chi _
  apply Finset.sum_le_sum_of_subset
  intro rho hr
  obtain ⟨hz, hstrip, hb⟩ := mem_zeroValues.mp hr
  exact mem_strictZeroValues.mpr ⟨hz, hstrip.1, hab.trans_le hb, hstrip.2⟩

theorem closed_lambda_le_strict_gate {q : ℕ} [NeZero q] {y lam d : ℝ}
    (hs : 0 < Real.log ((q : ℝ) * y)) (hlam : lam < d) :
    familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y ≤
      strictFamilyCount q (1 - d / Real.log ((q : ℝ) * y)) y := by
  apply closed_count_le_strict
  have hh := (div_lt_div_iff_of_pos_right hs).mpr hlam
  linarith

theorem countSegment_le_open_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a b C : ℝ} (hy : omegaCutoff N q ≤ y)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478)
    (hc : ∀ lam ∈ Set.Ioo a b,
      (familyCount q (1 - lam / Real.log ((q : ℝ) * y)) y : ℝ) ≤ C) :
    lambdaCountSegment N q y a b ≤
      C * lambdaSegment (sourceL N) (Real.log ((q : ℝ) * y)) a b := by
  have hn := Parameters.nat_pos_of_exp_le hN
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr hn
  have hn0' : (N : ℝ) ≠ 0 := hn0.ne'
  have hi : IntervalIntegrable
      (fun lam => C * (N : ℝ) ^ (-lam / Real.log ((q : ℝ) * y))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (lambdaCountIntegrand_integrable hN hy ha hab hb) hi (fun lam hlam => by
      unfold lambdaCountIntegrand
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hc lam hlam)
        (Real.rpow_nonneg hn0.le _))
  have hL : 0 ≤ sourceL N := by linarith [Parameters.sourceL_ge_3100 hN]
  have hs : 0 ≤ Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy]
  have hm := mul_le_mul_of_nonneg_left hh (div_nonneg hL hs)
  rw [intervalIntegral.integral_const_mul] at hm
  rw [lambdaSegment_eq_source_power hn]
  exact hm.trans_eq (by ring)

theorem countSegment_le_strict_gate {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) {y a b : ℝ} {C : ℕ}
    (hy : omegaCutoff N q ≤ y) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 0.478)
    (hc : strictFamilyCount q (1 - b / Real.log ((q : ℝ) * y)) y ≤ C) :
    lambdaCountSegment N q y a b ≤
      C * lambdaSegment (sourceL N) (Real.log ((q : ℝ) * y)) a b := by
  have hs : 0 < Real.log ((q : ℝ) * y) := by linarith [original_log_product_ge_ten hN hy]
  apply countSegment_le_open_cap hN hy ha hab hb
  intro lam hlam
  exact_mod_cast (closed_lambda_le_strict_gate hs hlam.2).trans hc

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.HeightCases
