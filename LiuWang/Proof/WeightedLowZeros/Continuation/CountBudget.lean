import LiuWang.Proof.WeightedLowZeros.Continuation.LogBudget

/-! # The frozen conductor mother pays a uniform 6.5 P log P low-height count -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem low_parameter_logs {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    24 ≤ Real.log (sourceP N) ∧
      Real.log (q : ℝ) + Real.log (omegaCutoff N q + 4) ≤ Real.log (sourceP N) + 2 := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hP := sourceP_pos hN'
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy := omegaCutoff_pos hN' (NeZero.pos q)
  have hL := sourceL_ge_3100 hN
  have hlog : 8 ≤ Real.log (sourceL N) := log_3100_bounds.1.trans
    (Real.log_le_log (by norm_num) hL)
  have hlogP : 24 ≤ Real.log (sourceP N) := by
    rw [sourceP, Real.log_pow]
    norm_num
    linarith
  have he2 : (7.36 : ℝ) ≤ Real.exp 2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      Real.exp_one_gt_d9.le 2
    have hid : Real.exp 2 = Real.exp 1 ^2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hid]
    exact (by norm_num : (7.36 : ℝ) ≤ 2.7182818283^2).trans hp
  have hlog736 : Real.log (7.36 : ℝ) ≤ 2 :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr he2
  have hmul : (q : ℝ) * (omegaCutoff N q + 4) ≤ 7.36 * sourceP N := by
    have he : (q : ℝ) * omegaCutoff N q = 3.36 * sourceP N := by
      unfold omegaCutoff
      field_simp
    nlinarith
  refine ⟨hlogP, ?_⟩
  have h := Real.log_le_log (mul_pos hq0 (by positivity)) hmul
  rw [Real.log_mul hq0.ne' (by positivity), Real.log_mul (by norm_num) hP.ne'] at h
  linarith

theorem characterBound_low_uniform {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    characterBound chi (omegaCutoff N q) ≤
      (2 * omegaCutoff N q + 4) * (Real.log (sourceP N) / 2 + 9/4) := by
  have hy : 0 ≤ omegaCutoff N q :=
    le_trans (by norm_num) (omegaCutoff_ge (NeZero.pos q) hq)
  obtain ⟨hlogP, hlog⟩ := low_parameter_logs hN hq
  have hqlog : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ q))
  unfold characterBound
  split_ifs with hc
  · unfold principalBound
    split_ifs with hy1
    · positivity
    · apply (min_le_right _ _).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hinv : 1 / (omegaCutoff N q + 3) ≤ 1/3 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
  · apply (nonprincipalBound_mono (Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) hy).trans
    have hl : Real.log (omegaCutoff N q + 3) ≤ Real.log (omegaCutoff N q + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    unfold nonprincipalBound
    apply mul_le_mul (by linarith) (by linarith) _ (by positivity)
    have hl0 : 0 ≤ Real.log (omegaCutoff N q + 3) :=
      Real.log_nonneg (by linarith)
    linarith

theorem countMother_low_uniform {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (a : ℝ) :
    countMother q (omegaCutoff N q) a ≤ 6.5 * sourceP N * Real.log (sourceP N) := by
  have hN' := exp_2000_le_of_exp_3100_le hN
  have hP := sourceP_pos hN'
  have hy := omegaCutoff_pos hN' (NeZero.pos q)
  have hlogP := (low_parameter_logs hN hq).1
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hcard : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have htot : (q.totient : ℝ) ≤ q := Nat.cast_le.mpr (Nat.totient_le q)
  calc
    _ ≤ ∑ chi : Character q, characterBound chi (omegaCutoff N q) :=
      Finset.sum_le_sum fun _ _ => min_le_left _ _
    _ ≤ ∑ _chi : Character q,
        (2 * omegaCutoff N q + 4) * (Real.log (sourceP N) / 2 + 9/4) :=
      Finset.sum_le_sum fun chi _ => characterBound_low_uniform hN hq chi
    _ = (q.totient : ℝ) *
        ((2 * omegaCutoff N q + 4) * (Real.log (sourceP N) / 2 + 9/4)) := by
      simp [hcard]
    _ ≤ (q : ℝ) * ((2 * omegaCutoff N q + 4) * (Real.log (sourceP N) / 2 + 9/4)) :=
      mul_le_mul_of_nonneg_right htot (by positivity)
    _ = (6.72 * sourceP N + 4 * q) * (Real.log (sourceP N) / 2 + 9/4) := by
      unfold omegaCutoff
      field_simp
      ring
    _ ≤ (10.72 * sourceP N) * (Real.log (sourceP N) / 2 + 9/4) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg hP.le (show 0 ≤ Real.log (sourceP N) - 24 by linarith)]

end LiuWang.Proof.WeightedLowZeros.Continuation
