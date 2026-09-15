import LiuWang.Proof.SourceRoute.ThirdArc.DensityIntegrals
import LiuWang.Proof.SourceRoute.ThirdArc.Heights

/-! The original beta layers (5.28), (5.38), with the split at 59/60. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc

theorem bandValues_beta_filter {q : ℕ} [NeZero q] (chi : Character q)
    (u v : ℝ) {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    (bandValues chi (1 / 2) u v).filter (fun rho => alpha ≤ rho.re) =
      bandValues chi alpha u v := by
  ext rho
  simp only [Finset.mem_filter, mem_bandValues]
  constructor
  · tauto
  · rintro ⟨hz, hs, hb, hh⟩
    exact ⟨⟨hz, hs, ha.trans hb, hh⟩, hb⟩

theorem upperMass_eq_band {q : ℕ} [NeZero q] (chi : Character q)
    (u v p : ℝ) {alpha : ℝ} (ha : 1 / 2 ≤ alpha) :
    upperMass (bandValues chi (1 / 2) u v) Complex.re
        (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) alpha =
      ∑ rho ∈ bandValues chi alpha u v,
        (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p) := by
  rw [upperMass, bandValues_beta_filter chi u v ha]

theorem character_beta_integrable {q : ℕ} [NeZero q] (chi : Character q)
    (u v p : ℝ) {X a b : ℝ} (hX : 0 < X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun alpha => betaKernel X alpha *
      ∑ rho ∈ bandValues chi alpha u v,
        (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) volume a b := by
  apply (upperMass_integrable (bandValues chi (1 / 2) u v) Complex.re
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p))
    ((betaKernel_continuous hX).intervalIntegrable a b)).congr_ae
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha halpha
  rw [Set.uIoc_of_le hab] at halpha
  dsimp only
  rw [upperMass_eq_band chi u v p (ha.trans halpha.1.le)]

theorem densityBand_beta_integrable (q : ℕ) [NeZero q] (u v p : ℝ)
    {X a b : ℝ} (hX : 0 < X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun alpha => betaKernel X alpha * densityBand q alpha u v p)
      volume a b := by
  simp only [densityBand, Finset.mul_sum]
  convert! IntervalIntegrable.sum (Finset.univ : Finset (Character q))
    (fun chi _ => character_beta_integrable chi u v p hX ha hab) using 1
  ext alpha
  simp only [Finset.sum_apply, Finset.mul_sum]

def betaMoment (q : ℕ) [NeZero q] (X u v p : ℝ) : ℝ :=
  ∑ chi : Character q, ∑ rho ∈ bandValues chi (1 / 2) u v,
    ((analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) * X ^ (rho.re - 1)

theorem character_beta_partialSummation {q : ℕ} [NeZero q] (chi : Character q)
    (u v p : ℝ) {X : ℝ} (hX : 0 < X) :
    (∑ rho ∈ bandValues chi (1 / 2) u v,
      ((analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) * X ^ (rho.re - 1)) =
      X ^ (-1 / 2 : ℝ) * (∑ rho ∈ bandValues chi (1 / 2) u v,
        (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p)) +
      ∫ alpha in (1 / 2 : ℝ)..1, betaKernel X alpha *
        ∑ rho ∈ bandValues chi alpha u v,
          (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p) := by
  have h := finite_beta_partialSummation (bandValues chi (1 / 2) u v) Complex.re
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ) * |rho.im| ^ (-p))
    hX (c := 1) (by
      intro rho hrho
      have hr := mem_bandValues.mp hrho
      exact ⟨hr.2.2.1, hr.2.1.2.1.le⟩)
  simp only [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_of_forall_mem measurableSet_uIoc
  intro alpha ha
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ha
  dsimp only
  rw [upperMass_eq_band chi u v p ha.1.le]

theorem betaMoment_partialSummation (q : ℕ) [NeZero q] (u v p : ℝ)
    {X : ℝ} (hX : 0 < X) :
    betaMoment q X u v p =
      X ^ (-1 / 2 : ℝ) * densityBand q (1 / 2) u v p +
        ∫ alpha in (1 / 2 : ℝ)..1, betaKernel X alpha * densityBand q alpha u v p := by
  simp only [betaMoment, densityBand, character_beta_partialSummation _ u v p hX,
    Finset.sum_add_distrib, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun chi _ =>
    by simpa only [Finset.mul_sum] using
      character_beta_integrable chi u v p hX le_rfl (by norm_num : (1 / 2 : ℝ) ≤ 1))]

theorem betaMoment_source_split (q : ℕ) [NeZero q] (u v p : ℝ)
    {X : ℝ} (hX : 0 < X) :
    betaMoment q X u v p =
      X ^ (-1 / 2 : ℝ) * densityBand q (1 / 2) u v p +
        (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
          betaKernel X alpha * densityBand q alpha u v p) +
        ∫ alpha in (59 / 60 : ℝ)..1,
          betaKernel X alpha * densityBand q alpha u v p := by
  rw [betaMoment_partialSummation q u v p hX,
    ← intervalIntegral.integral_add_adjacent_intervals
      (densityBand_beta_integrable q u v p hX (a := 1 / 2) (b := 59 / 60)
        le_rfl (by norm_num))
      (densityBand_beta_integrable q u v p hX (a := 59 / 60) (b := 1)
        (by norm_num) (by norm_num))]
  ring

theorem original_height_order {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N) :
    lowHeight ≤ middleHeight N q ∧ middleHeight N q ≤ sourceT N := by
  have hL := sourceL_pos hN
  have hL0 := sourceL_ge_2000 hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hL8 : 40 ≤ sourceL N ^ 8 := by
    have h := pow_le_pow_right₀ (one_le_sourceL hN) (by norm_num : 1 ≤ (8 : ℕ))
    simp only [pow_one] at h
    linarith
  have hpi : 10 * Real.pi ≤ 40 := by linarith [Real.pi_lt_four]
  constructor
  · unfold lowHeight middleHeight
    apply (le_div_iff₀ hq0).mpr
    calc
      10000 * Real.pi * (q : ℝ) ≤ 10000 * Real.pi * sourceL N ^ 6 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ 10 * Real.pi * sourceL N ^ 7 := by
        have h := mul_le_mul_of_nonneg_right
          (show 10000 * Real.pi ≤ 10 * Real.pi * sourceL N by nlinarith [Real.pi_pos])
          (pow_nonneg hL.le 6)
        exact h.trans_eq (by ring)
  · unfold middleHeight
    calc
      _ ≤ 10 * Real.pi * sourceL N ^ 7 :=
        div_le_self (by positivity) hq1
      _ ≤ sourceL N ^ 8 * sourceL N ^ 7 :=
        mul_le_mul_of_nonneg_right (hpi.trans hL8) (pow_nonneg hL.le 7)
      _ = sourceT N := by unfold sourceT; ring

theorem complete_band_eq_count_band {q : ℕ} [NeZero q] (chi : Character q)
    (u : ℝ) {v T : ℝ} (hv : v ≤ T) :
    (CompleteExpansion.zeroValues chi T).filter (fun rho => u ≤ |rho.im| ∧ |rho.im| ≤ v) =
      bandValues chi (1 / 2) u v := by
  ext rho
  simp only [Finset.mem_filter, CompleteExpansion.mem_zeroValues, mem_bandValues]
  constructor
  · tauto
  · rintro ⟨hz, ⟨h0, h1, hh⟩, ha, hu⟩
    exact ⟨⟨hz, h0, h1, hh.trans hv, ha⟩, hu, hh⟩

theorem middleKernel_eq_beta {N : ℕ} (hN : 0 < N) (rho : ℂ) :
    middleKernel N rho =
      16 * N * ((0.001 * (N : ℝ)) ^ (rho.re - 1) * |rho.im| ^ (-(1 / 2 : ℝ))) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [middleKernel, Real.mul_rpow (by norm_num) hn.le,
    Real.rpow_sub_one hn.ne', Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow]
  field_simp

theorem highKernel_eq_beta {N : ℕ} (hN : 0 < N) (rho : ℂ) :
    highKernel N rho =
      5 * N * ((N : ℝ) ^ (rho.re - 1) * |rho.im| ^ (-(1 : ℝ))) := by
  rw [highKernel, Real.rpow_sub_one (Nat.cast_pos.mpr hN).ne', Real.rpow_neg_one]
  field_simp

theorem sigma5_eq_betaMoment {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N) :
    sigma5 N q = (16 * N * Real.sqrt q / q.totient) *
      betaMoment q (0.001 * N) lowHeight (middleHeight N q) (1 / 2) := by
  simp only [sigma5, bandMass, complete_band_eq_count_band _
    lowHeight (original_height_order hN hq).2, betaMoment,
    middleKernel_eq_beta (nat_pos_of_exp_le hN)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem sigma6_eq_betaMoment {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sigma6 N q = (5 * N * Real.sqrt q / q.totient) *
      betaMoment q N (middleHeight N q) (sourceT N) 1 := by
  simp only [sigma6, bandMass, complete_band_eq_count_band _ (middleHeight N q) le_rfl,
    betaMoment, highKernel_eq_beta (nat_pos_of_exp_le hN), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  apply Finset.sum_congr rfl
  intro rho _
  ring

theorem equation_5_28 {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP1 N) :
    sigma5 N q = (16 * N * Real.sqrt q / q.totient) *
      ((0.001 * (N : ℝ)) ^ (-1 / 2 : ℝ) *
        densityBand q (1 / 2) lowHeight (middleHeight N q) (1 / 2) +
      (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
        betaKernel (0.001 * N) alpha * densityBand q alpha lowHeight (middleHeight N q) (1 / 2)) +
      ∫ alpha in (59 / 60 : ℝ)..1,
        betaKernel (0.001 * N) alpha * densityBand q alpha lowHeight (middleHeight N q) (1 / 2)) := by
  have hn := natCast_pos_of_exp_le hN
  rw [sigma5_eq_betaMoment hN hq, betaMoment_source_split]
  positivity

theorem equation_5_38 {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    sigma6 N q = (5 * N * Real.sqrt q / q.totient) *
      ((N : ℝ) ^ (-1 / 2 : ℝ) *
        densityBand q (1 / 2) (middleHeight N q) (sourceT N) 1 +
      (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
        betaKernel N alpha * densityBand q alpha (middleHeight N q) (sourceT N) 1) +
      ∫ alpha in (59 / 60 : ℝ)..1,
        betaKernel N alpha * densityBand q alpha (middleHeight N q) (sourceT N) 1) := by
  rw [sigma6_eq_betaMoment hN, betaMoment_source_split q _ _ _ (natCast_pos_of_exp_le hN)]

end LiuWang.Proof.SourceRoute.ThirdArc
