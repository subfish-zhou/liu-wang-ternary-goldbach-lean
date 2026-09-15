import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526.Consumer

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526

def lastRealRemainder (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    ∫ alpha in lastUpper q..1,
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha 0

theorem full_tail_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    exceptionalTailBill N q = originalLastBill N q +
      ((N : ℝ) * Real.sqrt q / q.totient) *
        ∫ alpha in lastUpper q..1,
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight := by
  have ho := last_interval_order hN hq
  have hx := natCast_pos_of_exp_le hN
  have hhalf : (1 : ℝ) / 2 ≤ lastLower q := by linarith [ho.1]
  have hi1 := family_low_integrable q lowHeight hx hhalf ho.2.1
  have hi2 := family_low_integrable q lowHeight hx (hhalf.trans ho.2.1) ho.2.2.le
  have hi := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  unfold exceptionalTailBill originalLastBill
  simp only [lastLower] at hi ⊢
  rw [← hi]
  ring

theorem familyCount_above_c1_eq_real {q : ℕ} [NeZero q] {alpha : ℝ}
    (halpha : lastUpper q < alpha)
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight)) < rho.re → rho.im = 0) :
    familyCount q alpha lowHeight = familyCount q alpha 0 := by
  have he (chi : Character q) : zeroValues chi alpha lowHeight = zeroValues chi alpha 0 := by
    ext rho
    simp only [mem_zeroValues]
    constructor
    · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
      have hr := hlocal chi rho hz h0 h1 hh (halpha.trans_le ha)
      exact ⟨hz, ⟨h0, h1, by simp [hr]⟩, ha⟩
    · rintro ⟨hz, ⟨h0, h1, hh⟩, ha⟩
      exact ⟨hz, ⟨h0, h1, hh.trans lowHeight_pos.le⟩, ha⟩
  simp only [familyCount, count, he]

theorem full_tail_eq_original_and_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight)) < rho.re → rho.im = 0) :
    exceptionalTailBill N q = originalLastBill N q + lastRealRemainder N q := by
  rw [full_tail_split hN hq]
  unfold lastRealRemainder
  congr 2
  have ho := last_interval_order hN hq
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ (fun alpha halpha => by
    rw [Set.uIoc_of_le ho.2.2.le] at halpha
    rw [familyCount_above_c1_eq_real halpha.1 hlocal])

theorem exceptionalTailBill_paid_with_real_remainder {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ lowHeight →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * lowHeight)) < rho.re → rho.im = 0) :
    exceptionalTailBill N q ≤ (3 / 100000 : ℝ) * (N : ℝ) / sourceL N +
      lastRealRemainder N q := by
  rw [full_tail_eq_original_and_real hN hq hlocal]
  linarith [equation_5_26_original hN hq hq1 htotient]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source525526
