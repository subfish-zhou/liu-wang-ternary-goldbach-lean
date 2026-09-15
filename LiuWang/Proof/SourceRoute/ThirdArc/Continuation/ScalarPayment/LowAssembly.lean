import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.LowBeta

/-! The two paid source pieces in the actual Sigma4, without deleting any real zero. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment

theorem low_character_integrable {q : ℕ} [NeZero q] (chi : Character q)
    {N : ℕ} (hN : 0 < N) (v : ℝ) :
    IntervalIntegrable (fun alpha => betaKernel N alpha * lowCoefficient alpha * count chi alpha v)
      volume (1 / 2) 1 := by
  have hi : IntervalIntegrable (fun alpha => betaKernel N alpha * count chi alpha v)
      volume (1 / 2) 1 := by
    simpa [bandValues, count] using
      character_beta_integrable chi 0 v 0 (Nat.cast_pos.mpr hN) le_rfl (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hc : ContinuousOn lowCoefficient (Set.uIcc (1 / 2 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact lowCoefficient_continuousOn (by norm_num)
  convert hi.mul_continuousOn hc using 1
  ext alpha
  ring

theorem low_family_partialSummation (q : ℕ) [NeZero q]
    {N : ℕ} (hN : 0 < N) (v : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ zeroValues chi (1 / 2) v,
      (analyticOrderNatAt chi.LFunction rho : ℝ) *
        (lowCoefficient rho.re * (N : ℝ) ^ (rho.re - 1))) ≤
      lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) * familyCount q (1 / 2) v +
        ∫ alpha in (1 / 2 : ℝ)..1,
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha v := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => low_character_partialSummation chi hN v)
  simp only [familyCount, Nat.cast_sum, Finset.mul_sum,
    intervalIntegral.integral_finsetSum (fun chi _ => low_character_integrable chi hN v),
    Finset.sum_add_distrib] at h ⊢
  exact h

theorem sigma4_eq_low_family {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sigma4 N q = ((N : ℝ) * Real.sqrt q / q.totient) *
      ∑ chi : Character q, ∑ rho ∈ zeroValues chi (1 / 2) lowHeight,
        (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (lowCoefficient rho.re * (N : ℝ) ^ (rho.re - 1)) := by
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hkernel (rho : ℂ) : lowKernel N rho =
      (N : ℝ) * (lowCoefficient rho.re * (N : ℝ) ^ (rho.re - 1)) := by
    simpa only [lowKernel, lowCoefficient, WeightedLowZeros.weight] using
      (WeightedLowZeros.weight_mul_endpoint (nat_pos_of_exp_le hN) rho.re).symm
  simp only [sigma4, bandMass, complete_band_eq_count_band _ 0 (hh.1.trans hh.2)]
  simp only [bandValues, abs_nonneg, Finset.filter_true, hkernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem sigma4_full_count_partialSummation {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sigma4 N q ≤ ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) * familyCount q (1 / 2) lowHeight +
        ∫ alpha in (1 / 2 : ℝ)..1,
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) := by
  rw [sigma4_eq_low_family hN hq1]
  exact mul_le_mul_of_nonneg_left
    (low_family_partialSummation q (nat_pos_of_exp_le hN) lowHeight) (by positivity)

def remainingLowBill (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    ((∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) +
      ∫ alpha in (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight))..1,
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight)

theorem low_bill_decomposition {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (lowCoefficient (1 / 2) * (N : ℝ) ^ (-1 / 2 : ℝ) * familyCount q (1 / 2) lowHeight +
        ∫ alpha in (1 / 2 : ℝ)..1,
          betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) =
      lowBetaBill N q + lowStripBill N q + remainingLowBill N q := by
  let a := 1 - 0.478 / Real.log ((q : ℝ) * lowHeight)
  let b := 1 - 0.2067 / Real.log ((q : ℝ) * lowHeight)
  have hs : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have ha : (59 / 60 : ℝ) ≤ a := M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  have hab : a ≤ b := sub_le_sub_left
    (div_le_div_of_nonneg_right (by norm_num : (0.2067 : ℝ) ≤ 0.478) hs.le) 1
  have hb : b ≤ 1 := sub_le_self _ (div_nonneg (by norm_num) hs.le)
  have hx := natCast_pos_of_exp_le hN
  have h1 := family_low_integrable q lowHeight hx (a := 1 / 2) (b := 59 / 60)
    le_rfl (by norm_num)
  have h2 := family_low_integrable q lowHeight hx (a := 59 / 60) (b := a) (by norm_num) ha
  have h3 := family_low_integrable q lowHeight hx
    ((by norm_num : (1 : ℝ) / 2 ≤ 59 / 60).trans ha) hab
  have h4 := family_low_integrable q lowHeight hx
    (((by norm_num : (1 : ℝ) / 2 ≤ 59 / 60).trans ha).trans hab) hb
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 (h2.trans (h3.trans h4)),
    ← intervalIntegral.integral_add_adjacent_intervals h2 (h3.trans h4),
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  unfold lowBetaBill lowStripBill remainingLowBill
  change _ = _ + _ + _
  dsimp only [a, b]
  ring

theorem sigma4_two_source_pieces_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    sigma4 N q ≤ 0.00368 * (N : ℝ) / sourceL N + remainingLowBill N q := by
  have h := sigma4_full_count_partialSummation hN hq1
  rw [low_bill_decomposition hN hq] at h
  have hb := equation_5_23_stronger hN hq1
  have hs := equation_5_25_stronger hN hq
  exact (h.trans (add_le_add (add_le_add hb hs) le_rfl)).trans_eq (by ring)

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment
