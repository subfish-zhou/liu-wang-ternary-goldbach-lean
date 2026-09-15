import LiuWang.Proof.Campaign20260915.SecondTerminal.SignedCells
import LiuWang.Proof.Campaign20260915.SecondTerminal.Endpoint14000
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.LowHeight.Assembly
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.LowAlpha
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.OriginalPayment

set_option autoImplicit false
noncomputable section
open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

def alphaMass (N q : ℕ) [NeZero q] (y a b : ℝ) : ℝ :=
  ∫ alpha in a..b,
    alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)

def heightMass (N q : ℕ) [NeZero q] (a b : ℝ → ℝ) : ℝ :=
  ∫ y in omegaCutoff N q..middleUpper N q, heightKernel y * alphaMass N q y (a y) (b y)

def lowAlphaMass (N q : ℕ) [NeZero q] : ℝ :=
  (0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) *
    bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
  ∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
    alphaKernel (0.001 * (N : ℝ)) alpha *
      bandMass q alpha (omegaCutoff N q) (middleUpper N q)

def lastStripLogBill (N q : ℕ) : ℝ :=
  (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
    ∫ z in lowerLog (sourceL N)..upperLog (sourceL N),
      lastKernel (sourceL N + Real.log 0.001) z

theorem alphaMass_add {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (y a b c : ℝ) :
    alphaMass N q y a c = alphaMass N q y a b + alphaMass N q y b c := by
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hi (u v : ℝ) : IntervalIntegrable
      (fun alpha => alphaKernel (0.001 * (N : ℝ)) alpha *
        (familyCount q alpha y : ℝ)) volume u v := by
    by_cases huv : u ≤ v
    · exact count_alpha_integrable hx huv y
    · exact (count_alpha_integrable hx (le_of_not_ge huv) y).symm
  exact (intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b c)).symm

theorem heightMass_add {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (a b c : ℝ → ℝ)
    (ha : ContinuousOn a (Set.Icc (omegaCutoff N q) (middleUpper N q)))
    (hb : ContinuousOn b (Set.Icc (omegaCutoff N q) (middleUpper N q)))
    (hc : ContinuousOn c (Set.Icc (omegaCutoff N q) (middleUpper N q)))
    (ha0 : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q), 1 / 2 ≤ a y)
    (hb0 : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q), 1 / 2 ≤ b y)
    (hc0 : ∀ y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q), 1 / 2 ≤ c y) :
    heightMass N q a c = heightMass N q a b + heightMass N q b c := by
  have hh := middle_height_domain hN hq
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have hk : ContinuousOn heightKernel (Set.uIcc (omegaCutoff N q) (middleUpper N q)) := by
    rw [Set.uIcc_of_le hh.2.1]
    exact continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (hh.1.trans_le hy.1)))
  have hiab := (moving_count_strip_integrable_unordered (q := q) hx hh.2.1
    ha hb ha0 hb0).mul_continuousOn hk
  have hibc := (moving_count_strip_integrable_unordered (q := q) hx hh.2.1
    hb hc hb0 hc0).mul_continuousOn hk
  unfold heightMass
  rw [← intervalIntegral.integral_add
    (by simpa only [alphaMass, mul_comm] using hiab)
    (by simpa only [alphaMass, mul_comm] using hibc)]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [← mul_add, ← alphaMass_add hN]

theorem original_height_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    heightMass N q (fun _ => 59 / 60) (fun _ => 1) =
      LowHeight.actualM1 N q + actualStripIntegral N q +
        heightMass N q (stripUpper q) (siegelCutoff q) +
          heightMass N q (siegelCutoff q) (fun _ => 1) := by
  have hs := strip_bounds_continuous hN hq
  have ht := siegelCutoff_continuous hN hq
  have hlower (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
      1 / 2 ≤ stripLower q y := by
    have hd := middle_log_domain hN hq hy
    have hb := div_le_self (by norm_num : (0 : ℝ) ≤ 0.478) hd.2.1
    unfold stripLower
    linarith
  have hupper (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
      1 / 2 ≤ stripUpper q y :=
    (sparse_cutoff_order (middle_log_domain hN hq hy).2.1).1
  have hcut (y : ℝ) (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
      1 / 2 ≤ siegelCutoff q y :=
    (hupper y hy).trans (sparse_cutoff_order (middle_log_domain hN hq hy).2.1).2.1
  have h1 := heightMass_add hN hq (fun _ => 59 / 60) (stripLower q) (fun _ => 1)
    continuousOn_const hs.1 continuousOn_const (by intros; norm_num)
    hlower (by intros; norm_num)
  have h2 := heightMass_add hN hq (stripLower q) (stripUpper q) (fun _ => 1)
    hs.1 hs.2 continuousOn_const hlower hupper (by intros; norm_num)
  have h3 := heightMass_add hN hq (stripUpper q) (siegelCutoff q) (fun _ => 1)
    hs.2 ht continuousOn_const hupper hcut (by intros; norm_num)
  change heightMass N q (fun _ => 59 / 60) (fun _ => 1) =
    LowHeight.actualM1 N q + heightMass N q (stripLower q) (fun _ => 1) at h1
  change heightMass N q (stripLower q) (fun _ => 1) =
    actualStripIntegral N q + heightMass N q (stripUpper q) (fun _ => 1) at h2
  linarith only [h1, h2, h3]

theorem source_57_original_coefficients {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (16 * (N : ℝ) * Real.sqrt q / q.totient) *
        (lowAlphaMass N q +
          (1 / Real.sqrt (middleUpper N q)) *
            alphaMass N q (middleUpper N q) (59 / 60) 1) +
        (8 * (N : ℝ) * Real.sqrt q / q.totient) *
          heightMass N q (fun _ => 59 / 60) (fun _ => 1) := by
  have hp := source_57_middle_packet hN hq ha eta
  change ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
    (10 * (N : ℝ) * Real.sqrt q / q.totient) *
      (lowAlphaMass N q +
        (1 / Real.sqrt (middleUpper N q)) *
          alphaMass N q (middleUpper N q) (59 / 60) 1 +
        (1 / 2 : ℝ) * heightMass N q (fun _ => 59 / 60) (fun _ => 1)) at hp
  have hn := norm_nonneg (middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta)
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith only [hp, hn]

theorem original_packet_reduction {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hseven : ∀ y : ℝ, densityGate q ≤ y → ∀ alpha : ℝ,
      1 / 2 ≤ alpha → alpha < 1 →
        (familyCount q alpha y : ℝ) ≤ Applications.sourceSevenBound q alpha y)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      0.00104 * (N : ℝ) / sourceL N +
      (N : ℝ) * ((32281 : ℝ) / 1000000 + 8 * LowHeight.originalLowScalar (sourceL N)) /
        sourceL N +
      0.000021 * (N : ℝ) / sourceL N +
      lastStripLogBill N q + endpointDensityBill N q +
      0.0000045 * (N : ℝ) / sourceL N +
      (16 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((1 / Real.sqrt (middleUpper N q)) *
          alphaMass N q (middleUpper N q) (siegelCutoff q (middleUpper N q)) 1) +
      (8 * (N : ℝ) * Real.sqrt q / q.totient) *
        heightMass N q (siegelCutoff q) (fun _ => 1) := by
  have hp := source_57_original_coefficients hN hq ha eta
  rw [original_height_split hN hq, alphaMass_add hN (middleUpper N q)
    (59 / 60) (siegelCutoff q (middleUpper N q)) 1] at hp
  have hlo := mul_le_mul_of_nonneg_left (actual_low_alpha_normalized hN hq)
    (show 0 ≤ (16 : ℝ) * N by positivity)
  simp only [neg_div] at hlo
  change 16 * (N : ℝ) * ((Real.sqrt q / q.totient) * lowAlphaMass N q) ≤ _ at hlo
  have hm1 := mul_le_mul_of_nonneg_left
    (LowHeight.actual_M1_le_original_low_scalar hN hq hseven hnu) (Nat.cast_nonneg N)
  have h516 := actual_516_payment_of_source_totient hN hq hnu
  have h517 := actual_last_strip_log_bound_T2 hN hq
  change (8 * (N : ℝ) * Real.sqrt q / q.totient) *
    heightMass N q (stripUpper q) (siegelCutoff q) ≤ lastStripLogBill N q at h517
  have hep := truncated_endpoint_density_remaining hN hq hseven
  change (16 * (N : ℝ) * Real.sqrt q / q.totient) *
    ((1 / Real.sqrt (middleUpper N q)) *
      alphaMass N q (middleUpper N q) (59 / 60) (siegelCutoff q (middleUpper N q))) ≤
        endpointDensityBill N q + 0.0000045 * (N : ℝ) / sourceL N at hep
  simp only [div_eq_mul_inv] at hp hlo hm1 h516 h517 hep ⊢
  nlinarith only [hp, hlo, hm1, h516, h517, hep]

#print axioms original_height_split
#print axioms source_57_original_coefficients
#print axioms original_packet_reduction

end LiuWang.Proof.Campaign20260915.SecondTerminal
