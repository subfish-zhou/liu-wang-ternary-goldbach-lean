import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.Count23Principal

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight

theorem source23_le_source24 {q y : ℝ} (hq : 700000 ≤ q) (hy : 3.36 ≤ y) :
    source23Envelope y ≤ source24Envelope q y := by
  have hq0 : 0 < q := by linarith
  have hy0 : 0 < y := by linarith
  have hlq : 13 ≤ Real.log q := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ (12 : ℕ))
      (by norm_num at *; linarith : (3 : ℝ) ^ (12 : ℕ) ≤ q)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_three_gt_d9]
  have hqdiv : 4 ≤ Real.log q / Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
  have hm := mul_le_mul_of_nonneg_right hqdiv hy0.le
  have hly := Real.log_le_sub_one_of_pos hy0
  unfold source23Envelope source24Envelope
  rw [Real.log_mul hq0.ne' hy0.ne']
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm, hly, hlq, hy]

theorem familyCount_le_source24 {q : ℕ} [NeZero q] {alpha y : ℝ}
    (hq : (700000 : ℝ) ≤ q) (ha : 0 ≤ alpha) (hy : 3.36 ≤ y) :
    (familyCount q alpha y : ℝ) ≤ q.totient * source24Envelope q y := by
  classical
  have hc : Fintype.card (Character q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  unfold familyCount
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _chi : Character q, source24Envelope q y := by
      apply Finset.sum_le_sum
      intro chi _
      by_cases hh : chi = 1
      · subst chi
        exact (count_principal_le_source23 q ha hy).trans (source23_le_source24 hq hy)
      · exact count_nonprincipal_le_source24 hh ha hy
    _ = _ := by simp [hc]

theorem actual_low_inner_source24 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hgate : omegaCutoff N q ≤ densityGate q) {y : ℝ}
    (hy : y ∈ Set.Icc (omegaCutoff N q) (densityGate q)) :
    (∫ alpha in (59 / 60 : ℝ)..stripLower q y,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) ≤
      (q.totient * source24Envelope q y) *
        Real.exp (-0.478 * (sourceL N + Real.log 0.001) / Real.log ((q : ℝ) * y)) := by
  have hqbig := low_gate_modulus_lower hN hq hgate
  have hymin : 3.36 ≤ y := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have hh : 3.36 ≤ omegaCutoff N q := by
      apply (le_div_iff₀ hq0).mpr
      linarith
    exact hh.trans hy.1
  have hc (alpha : ℝ) (ha : 0 ≤ alpha) :=
    familyCount_le_source24 hqbig ha hymin
  have hi := actual_inner_le_count_bound hN
    ((Nat.cast_nonneg (familyCount q 0 y)).trans (hc 0 le_rfl))
    (fun alpha ha => hc alpha (by linarith))
  rwa [log_window_eq (nat_pos_of_exp_le hN)] at hi

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight
