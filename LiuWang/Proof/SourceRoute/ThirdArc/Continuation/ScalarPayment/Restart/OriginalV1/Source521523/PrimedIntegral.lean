import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523.LocalSplit

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523

def originalPrimedBill (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    (lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) * familyCount q (1 / 2) lowHeight +
      ∫ alpha in (1 / 2 : ℝ)..Source525526.lastUpper q,
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight)

theorem rectangle_upperMass (q : ℕ) [NeZero q] {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    upperMass (rectangleZeros q (1 / 2) lowHeight) (fun z => z.2.re)
      (fun z => (analyticOrderNatAt z.1.LFunction z.2 : ℝ)) alpha =
        familyCount q alpha lowHeight := by
  rw [familyCount_rectangle ha le_rfl]
  unfold upperMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hh := (mem_zeroValues.mp (rectangle_mem.mp hz)).2.1.2.2
  simp only [hh, and_true]

theorem primed_upperMass_le_family (q : ℕ) [NeZero q]
    (e : Option ((_chi : Character q) × ℂ)) {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    upperMass (primedZeros q e) (fun z => z.2.re)
      (fun z => (analyticOrderNatAt z.1.LFunction z.2 : ℝ)) alpha ≤
        familyCount q alpha lowHeight := by
  rw [← rectangle_upperMass q ha]
  unfold upperMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
  · intro z _ _
    exact Nat.cast_nonneg _

theorem primedSigma4_le_original_bill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    {e : Option ((_chi : Character q) × ℂ)} (hloc : LocalC1Data q e) :
    primedSigma4 N q e ≤ originalPrimedBill N q := by
  have hn := natCast_pos_of_exp_le hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have ho := Source525526.last_interval_order hN hq
  have hab : (1 / 2 : ℝ) ≤ Source525526.lastUpper q := by linarith [ho.1, ho.2.1]
  have hp := finite_low_partialSummation (primedZeros q e) (fun z => z.2.re)
    (fun z => (analyticOrderNatAt z.1.LFunction z.2 : ℝ))
    (X := N) (a := 1 / 2) (c := Source525526.lastUpper q) hN1 (by norm_num) hab
    (by
      intro z hz
      exact ⟨(mem_zeroValues.mp (rectangle_mem.mp (Finset.mem_filter.mp hz).1)).2.2,
        primed_right_boundary hloc hz⟩)
    (fun _ _ => Nat.cast_nonneg _)
  have hmass : (∑ z ∈ primedZeros q e, (analyticOrderNatAt z.1.LFunction z.2 : ℝ)) ≤
      familyCount q (1 / 2) lowHeight := by
    have he : upperMass (primedZeros q e) (fun z => z.2.re)
        (fun z => (analyticOrderNatAt z.1.LFunction z.2 : ℝ)) (1 / 2) =
        ∑ z ∈ primedZeros q e, (analyticOrderNatAt z.1.LFunction z.2 : ℝ) := by
      unfold upperMass
      congr 1
      apply Finset.filter_eq_self.mpr
      intro z hz
      exact (mem_zeroValues.mp (rectangle_mem.mp (Finset.mem_filter.mp hz).1)).2.2
    rw [← he]
    exact primed_upperMass_le_family q e le_rfl
  have hb := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ lowCoefficient (1 / 2) * (N : ℝ) ^ ((1 / 2 : ℝ) - 1) from
      mul_nonneg (lowCoefficient_nonneg (by norm_num)) (Real.rpow_nonneg hn.le _))
  have hi :
      (∫ alpha in (1 / 2 : ℝ)..Source525526.lastUpper q,
        (betaKernel N alpha * lowCoefficient alpha) *
          upperMass (primedZeros q e) (fun z => z.2.re)
            (fun z => (analyticOrderNatAt z.1.LFunction z.2 : ℝ)) alpha) ≤
      ∫ alpha in (1 / 2 : ℝ)..Source525526.lastUpper q,
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight := by
    apply intervalIntegral.integral_mono_on hab
      (upperMass_integrable _ _ _ (low_integrand_integrable hn (by norm_num) hab))
      (family_low_integrable q lowHeight hn le_rfl hab)
    intro alpha ha
    apply mul_le_mul_of_nonneg_left (primed_upperMass_le_family q e ha.1)
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hn.le _) (Real.log_nonneg hN1))
      (lowCoefficient_nonneg (by linarith [ha.1]))
  have h := hp.trans (add_le_add hb hi)
  have h := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (N : ℝ) * Real.sqrt q / q.totient by positivity)
  simpa only [primedSigma4, originalPrimedBill,
    show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] using h

theorem original_finite_bill_decomposition {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    originalPrimedBill N q =
      lowBetaBill N q +
        ((N : ℝ) * Real.sqrt q / q.totient) *
          (∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
            betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) +
        lowStripBill N q + Source525526.originalLastBill N q := by
  let a := 1 - 0.478 / Real.log ((q : ℝ) * lowHeight)
  let b := Source525526.lastLower q
  let c := Source525526.lastUpper q
  have ha : (59 / 60 : ℝ) ≤ a := M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  have ht : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have hab : a ≤ b := sub_le_sub_left
    (div_le_div_of_nonneg_right (by norm_num : (0.2067 : ℝ) ≤ 0.478) ht.le) 1
  have hbc : b ≤ c := (Source525526.last_interval_order hN hq).2.1
  have hx := natCast_pos_of_exp_le hN
  have h1 := family_low_integrable q lowHeight hx (a := 1 / 2) (b := 59 / 60)
    le_rfl (by norm_num)
  have h2 := family_low_integrable q lowHeight hx (a := 59 / 60) (b := a) (by norm_num) ha
  have h3 := family_low_integrable q lowHeight hx
    ((by norm_num : (1 : ℝ) / 2 ≤ 59 / 60).trans ha) hab
  have h4 := family_low_integrable q lowHeight hx
    (((by norm_num : (1 : ℝ) / 2 ≤ 59 / 60).trans ha).trans hab) hbc
  unfold originalPrimedBill
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 (h2.trans (h3.trans h4)),
    ← intervalIntegral.integral_add_adjacent_intervals h2 (h3.trans h4),
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  unfold lowBetaBill lowStripBill Source525526.originalLastBill
  dsimp only [a, b, c, Source525526.lastLower]
  ring

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1.Source521523
