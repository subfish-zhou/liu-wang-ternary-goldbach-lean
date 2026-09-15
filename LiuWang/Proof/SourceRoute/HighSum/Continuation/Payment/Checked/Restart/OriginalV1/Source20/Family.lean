import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20.DecimalBounds
import LiuWang.Proof.SourceRoute.HighSum.SourceReduction

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.WeightedHighZeros.Continuation

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20

theorem family_signed_decimal (q : ℕ) [NeZero q] {alpha y : ℝ}
    (ha : 1 / 2 ≤ alpha) (hy : 3.36 ≤ y) :
    (familyCount q alpha y : ℝ) ≤
      principalDecimal y + (q.totient - 1 : ℕ) * nonprincipalDecimal q y := by
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold familyCount
  rw [Nat.cast_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q))]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)).erase 1)
    (fun chi hchi => nonprincipal_count_decimal (Finset.mem_erase.mp hchi).1 ha hy)
  have hp := principal_count_decimal q ha hy
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hc, nsmul_eq_mul] at hh
  linarith

theorem nonprincipalDecimal_mono {Q R y : ℝ} (hQ : 0 < Q) (hQR : Q ≤ R)
    (hy : 0 < y) : nonprincipalDecimal Q y ≤ nonprincipalDecimal R y := by
  have hh := Real.log_le_log (mul_pos hQ hy) (mul_le_mul_of_nonneg_right hQR hy.le)
  have h1 := mul_le_mul_of_nonneg_left hh (div_nonneg hy.le Real.pi_pos.le)
  unfold nonprincipalDecimal
  linarith

theorem principal_le_real_decimal {Q y : ℝ} (hQ : 0 < Q)
    (hlog : 10 ≤ Real.log Q) (hy : 0 < y) :
    principalDecimal y ≤ nonprincipalDecimal Q y := by
  have hc : 5 / 2 ≤ Real.log Q / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_four]
  have hm : 5 / 2 * y ≤ y / Real.pi * Real.log Q := by
    calc
      _ ≤ Real.log Q / Real.pi * y := mul_le_mul_of_nonneg_right hc hy.le
      _ = _ := by ring
  have ht := Real.log_le_sub_one_of_pos hy
  unfold principalDecimal nonprincipalDecimal
  rw [Real.log_mul hQ.ne' hy.ne']
  nlinarith

theorem real_decimal_nonneg {Q y : ℝ} (hQ : 0 < Q)
    (hlog : 10 ≤ Real.log Q) (hy : 3.36 ≤ y) :
    0 ≤ nonprincipalDecimal Q y := by
  exact (Nat.cast_nonneg (count (1 : Character 1) (1 / 2) y)).trans
    ((principal_count_decimal 1 (by norm_num) hy).trans
      (principal_le_real_decimal hQ hlog (by linarith)))

theorem signed_real_parameter (q : ℕ) [NeZero q] {Q y : ℝ}
    (hQ : 0 < Q) (hlog : 10 ≤ Real.log Q) (hq : (q : ℝ) ≤ Q)
    (hy : 3.36 ≤ y) :
    principalDecimal y + (q.totient - 1 : ℕ) * nonprincipalDecimal q y ≤
      Q * nonprincipalDecimal Q y := by
  have hp := principal_le_real_decimal hQ hlog (by linarith : 0 < y)
  have hn := nonprincipalDecimal_mono (Nat.cast_pos.mpr (NeZero.pos q)) hq
    (by linarith : 0 < y)
  have htot : (q.totient - 1 : ℕ) + 1 = q.totient :=
    Nat.sub_add_cancel (Nat.totient_pos.mpr (NeZero.pos q))
  have htotR : ((q.totient - 1 : ℕ) : ℝ) + 1 = (q.totient : ℝ) := by
    exact_mod_cast htot
  have hphi : (q.totient : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (Nat.totient_le q)).trans hq
  have hh := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (q.totient - 1))
  have hcard := mul_le_mul_of_nonneg_right hphi (real_decimal_nonneg hQ hlog hy)
  rw [← htotR] at hcard
  nlinarith

theorem family_real_parameter (q : ℕ) [NeZero q] {Q alpha y : ℝ}
    (hQ : 0 < Q) (hlog : 10 ≤ Real.log Q) (hq : (q : ℝ) ≤ Q)
    (ha : 1 / 2 ≤ alpha) (hy : 3.36 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ Q * nonprincipalDecimal Q y :=
  (family_signed_decimal q ha hy).trans (signed_real_parameter q hQ hlog hq hy)

theorem source19_signed_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    sourceMass N q alpha ≤
      (principalDecimal (sourceT N) +
        (q.totient - 1 : ℕ) * nonprincipalDecimal q (sourceT N)) / sourceT N +
      ∫ y in omegaCutoff N q..sourceT N, heightKernel y *
        (principalDecimal y + (q.totient - 1 : ℕ) * nonprincipalDecimal q y) := by
  have hu := Parameters.omegaCutoff_ge (NeZero.pos q) hq
  have huT := WeightedLowZeros.omegaCutoff_le_sourceT (q := q) hN
  have hu0 : 0 < omegaCutoff N q := by linarith
  have hT0 : 0 < sourceT N := hu0.trans_le huT
  have hT := family_signed_decimal q ha (hu.trans huT)
  have hi : IntervalIntegrable (fun y => heightKernel y *
      (principalDecimal y + (q.totient - 1 : ℕ) * nonprincipalDecimal q y))
      MeasureTheory.volume (omegaCutoff N q) (sourceT N) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huT]
    apply ContinuousOn.mul
    · exact continuousOn_const.div (continuousOn_id.pow 2)
        (fun y hy => pow_ne_zero _ (ne_of_gt (hu0.trans_le hy.1)))
    · unfold principalDecimal nonprincipalDecimal
      have hl : ContinuousOn Real.log (Set.Icc (omegaCutoff N q) (sourceT N)) :=
        continuousOn_id.log (fun y hy => (hu0.trans_le hy.1).ne')
      have hlq : ContinuousOn (fun y : ℝ => Real.log ((q : ℝ) * y))
          (Set.Icc (omegaCutoff N q) (sourceT N)) :=
        (continuousOn_const.mul continuousOn_id).log (fun y hy =>
          mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q)) (hu0.trans_le hy.1).ne')
      fun_prop
  apply (sourceMass_le_full_height hN hq alpha).trans
  apply add_le_add (div_le_div_of_nonneg_right hT hT0.le)
  apply intervalIntegral.integral_mono_on huT (family_height_integrable q alpha hu0 huT) hi
  intro y hy
  exact mul_le_mul_of_nonneg_left (family_signed_decimal q ha (hu.trans hy.1))
    (by unfold heightKernel; positivity)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Restart.OriginalV1.Source20
