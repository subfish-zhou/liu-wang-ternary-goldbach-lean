import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.Payment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment

theorem count_alpha_integrable_any {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 < x)
    (a b y : ℝ) :
    IntervalIntegrable (fun alpha => alphaKernel x alpha * (familyCount q alpha y : ℝ))
      volume a b := by
  rcases le_total a b with hab | hba
  · exact count_alpha_integrable hx hab y
  · exact (count_alpha_integrable hx hba y).symm

theorem moving_strip_integrable_any {q : ℕ} [NeZero q] {x u v : ℝ}
    (hx : 0 < x) (huv : u ≤ v) {a b : ℝ → ℝ}
    (ha : ContinuousOn a (Set.Icc u v)) (hb : ContinuousOn b (Set.Icc u v))
    (ha0 : ∀ y ∈ Set.Icc u v, 1 / 2 ≤ a y)
    (hb0 : ∀ y ∈ Set.Icc u v, 1 / 2 ≤ b y) :
    IntervalIntegrable (fun y => ∫ alpha in a y..b y,
      alphaKernel x alpha * (familyCount q alpha y : ℝ)) volume u v := by
  have hia := moving_count_strip_integrable (q := q) hx huv continuousOn_const ha
    (fun _ _ => le_rfl) ha0
  have hib := moving_count_strip_integrable (q := q) hx huv continuousOn_const hb
    (fun _ _ => le_rfl) hb0
  apply (hib.sub hia).congr
  intro y _
  have h := intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable_any (q := q) hx (1 / 2) (a y) y)
    (count_alpha_integrable_any (q := q) hx (a y) (b y) y)
  dsimp only
  linarith only [h]

theorem source_strip_endpoint_bounds {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
    1 / 2 ≤ stripLower q y ∧ stripLower q y ≤ stripUpper q y ∧ stripUpper q y ≤ 1 := by
  have hd := middle_log_domain hN hq hy
  have hdiv : 0.478 / Real.log ((q : ℝ) * y) ≤ (0.478 : ℝ) :=
    div_le_self (by norm_num) hd.2.1
  refine ⟨?_, strip_order hd.1, ?_⟩
  · unfold stripLower
    linarith
  · unfold stripUpper
    apply sub_le_self
    exact div_nonneg (by norm_num) (by linarith [hd.2.1])

theorem source_other_strips_integrable {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    IntervalIntegrable (fun y => heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))
      volume (omegaCutoff N q) (middleUpper N q) ∧
    IntervalIntegrable (fun y => heightKernel y *
      ∫ alpha in stripUpper q y..1,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))
      volume (omegaCutoff N q) (middleUpper N q) := by
  have hh := middle_height_domain hN hq
  have hNp := natCast_pos_of_exp_le hN
  have hs := strip_bounds_continuous hN hq
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hk : ContinuousOn heightKernel (Set.uIcc (omegaCutoff N q) (middleUpper N q)) := by
    rw [Set.uIcc_of_le hh.2.1]
    exact continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  have hl := moving_strip_integrable_any (q := q) hx hh.2.1 continuousOn_const hs.1
    (fun _ _ => by norm_num : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      (1 / 2 : ℝ) ≤ 59 / 60)
    (fun y hy => (source_strip_endpoint_bounds hN hq hy).1)
  have hu := moving_strip_integrable_any (q := q) hx hh.2.1 hs.2 continuousOn_const
    (fun y hy => (source_strip_endpoint_bounds hN hq hy).1.trans
      (source_strip_endpoint_bounds hN hq hy).2.1)
    (fun _ _ => by norm_num : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q),
      (1 / 2 : ℝ) ≤ 1)
  exact ⟨by simpa only [mul_comm] using hl.mul_continuousOn hk,
    by simpa only [mul_comm] using hu.mul_continuousOn hk⟩

theorem source_density_three_strips {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
      ∫ alpha in (59 / 60 : ℝ)..1,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) =
      (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
        ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
      actualStripIntegral N q +
      (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
        ∫ alpha in stripUpper q y..1,
          alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) := by
  have hNp := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have ho := source_other_strips_integrable hN hq
  have hi := actualStrip_integrable hN hq
  rw [actualStripIntegral, ← intervalIntegral.integral_add ho.1 hi,
    ← intervalIntegral.integral_add (ho.1.add hi) ho.2]
  apply intervalIntegral.integral_congr
  intro y _
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable_any (q := q) hx (59 / 60) (stripLower q y) y)
    (count_alpha_integrable_any (q := q) hx (stripLower q y) (stripUpper q y) y)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable_any (q := q) hx (59 / 60) (stripUpper q y) y)
    (count_alpha_integrable_any (q := q) hx (stripUpper q y) 1 y)
  dsimp only
  rw [← mul_add, ← mul_add, h1, h2]

theorem source_57_packet_with_516_paid {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) *
            bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
          (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              bandMass q alpha (omegaCutoff N q) (middleUpper N q)) +
          (1 / Real.sqrt (middleUpper N q)) *
            (∫ alpha in (59 / 60 : ℝ)..1,
              alphaKernel (0.001 * (N : ℝ)) alpha *
                (familyCount q alpha (middleUpper N q) : ℝ))) +
      (5 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
            ∫ alpha in (59 / 60 : ℝ)..stripLower q y,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
          (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
            ∫ alpha in stripUpper q y..1,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ))) +
      0.0000111104 * (N : ℝ) / sourceL N := by
  have hp := source_57_middle_packet hN hq ha eta
  rw [source_density_three_strips hN hq] at hp
  have hpay := strong_kernel_strip_payment hN hq
  simp only [div_eq_mul_inv] at hp hpay ⊢
  nlinarith only [hp, hpay]

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment
