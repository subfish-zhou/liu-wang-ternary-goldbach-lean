import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining.Domain

/-! Gauss/phi、同 q 倒 eta 因子和逐字符导子计数一起支付整个大模数低高度余包。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion

def gaussCap (q : ℕ) : ℝ := min (Real.sqrt (q : ℝ)) (q.totient : ℝ)

def sharpGaussMass (q : ℕ) [NeZero q] (a : ℕ) (y : ℝ) : ℝ :=
  (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ * sharpCount chi y

def lowKernel (N q : ℕ) : ℝ := 9 * (q : ℝ) * (N : ℝ) / sourceP N

def packetFee (N a q : ℕ) [NeZero q] : ℝ :=
  lowKernel N q *
    (gaussCap q / (q.totient : ℝ) * (7 + 14000 * innerWeight N) +
      outerWeight N * sharpGaussMass q a (lowHeight N q))

theorem norm_G_le_cap {a q : ℕ} [NeZero q] (hi : sourceIndex a q) (chi : Character q) :
    ‖G a chi‖ ≤ gaussCap q := by
  apply le_min _ (norm_G_le_totient a chi)
  exact (norm_G_le_sqrt_conductor hi.2.2 chi).trans (Real.sqrt_le_sqrt
    (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi))

theorem sharpGaussMass_le_conductor {a q : ℕ} [NeZero q] (hi : sourceIndex a q)
    {y : ℝ} (hy : 0 ≤ y) :
    sharpGaussMass q a y ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, Real.sqrt chi.conductor * sharpCount chi y := by
  unfold sharpGaussMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro chi _
  have hc : 0 ≤ sharpCount chi y :=
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)).trans (complete_count_le_sharp chi hy)
  exact mul_le_mul_of_nonneg_right (norm_G_le_sqrt_conductor hi.2.2 chi) hc

theorem Jrho_largeLow_weight {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ largeLowValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) * lowKernel N q := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hP := sourceP_pos hN0
  have hb := (mem_zeroValues.mp (largeLow_subset_zero chi positive hr)).2.2.1.le
  have ht := (Finset.mem_filter.mp hr).2
  have he0 : eta ≠ 0 := abs_pos.mp ((deltaRadius_pos hN0 (NeZero.pos q)).trans he)
  by_cases hg : rho.im = 0
  · calc
      _ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|) :=
        OscillatoryBounds.Jrho_real_reciprocal (nat_pos_of_exp_le hN) hb hg he0
      _ = (0.001 * (N : ℝ)) ^ (rho.re - 1) * (1 / (Real.pi * |eta|)) := by ring
      _ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) * (3 * (q : ℝ) * (N : ℝ) / sourceP N) :=
        mul_le_mul_of_nonneg_left (reciprocal_same_q hN0 he) (by positivity)
      _ ≤ _ := by unfold lowKernel; gcongr; norm_num
  · calc
      _ ≤ (3 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |eta| :=
        OscillatoryBounds.Jrho_far_three_pi (nat_pos_of_exp_le hN) hb hg
          (tiny_height_is_far hN0 (NeZero.pos q) he ht)
      _ = (3 * (0.001 * (N : ℝ)) ^ (rho.re - 1)) * (1 / (Real.pi * |eta|)) := by ring
      _ ≤ (3 * (0.001 * (N : ℝ)) ^ (rho.re - 1)) * (3 * (q : ℝ) * (N : ℝ) / sourceP N) :=
        mul_le_mul_of_nonneg_left (reciprocal_same_q hN0 he) (by positivity)
      _ = _ := by unfold lowKernel; ring

theorem Jrho_close {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ closeValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) : ‖Jrho N rho eta‖ ≤ lowKernel N q := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hr := (Finset.mem_filter.mp hr).1
  have hb := (mem_zeroValues.mp (largeLow_subset_zero chi positive hr)).2.2.1.le
  have hw : (0.001 * (N : ℝ)) ^ (rho.re - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (sourceWindow_gt_one (exp_2000_le_of_exp_3100_le hN)).le (sub_nonpos.mpr hb)
  exact (Jrho_largeLow_weight hN hr he).trans
    ((mul_le_mul_of_nonneg_right hw (by unfold lowKernel; positivity)).trans_eq (one_mul _))

theorem Jrho_middle {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ middleValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ innerWeight N * lowKernel N q := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  obtain ⟨hr, hb, _⟩ := Finset.mem_filter.mp hr
  exact (Jrho_largeLow_weight hN hr he).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (sourceWindow_gt_one (exp_2000_le_of_exp_3100_le hN)).le
      (sub_le_sub_right hb.le 1)) (by unfold lowKernel; positivity))

theorem Jrho_left {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ leftValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ outerWeight N * lowKernel N q := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  obtain ⟨hr, _, hb⟩ := Finset.mem_filter.mp hr
  exact (Jrho_largeLow_weight hN hr he).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (sourceWindow_gt_one (exp_2000_le_of_exp_3100_le hN)).le
      (sub_le_sub_right hb.le 1)) (by unfold lowKernel; positivity))

theorem norm_packet_le_cap_count {N a q : ℕ} [NeZero q] (hi : sourceIndex a q)
    (values : Character q → Finset ℂ) {eta B C : ℝ} (hB : 0 ≤ B)
    (hJ : ∀ chi rho, rho ∈ values chi → ‖Jrho N rho eta‖ ≤ B)
    (hC : (∑ chi : Character q, ∑ rho ∈ values chi, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ C) :
    ‖realPacketOn q a values N eta‖ ≤ gaussCap q / (q.totient : ℝ) * C * B := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hg : 0 ≤ gaussCap q := le_min (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  apply (norm_realPacketOn_le_weighted values hJ).trans
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, gaussCap q *
        ((∑ rho ∈ values chi, (analyticOrderNatAt chi.LFunction rho : ℝ)) * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      exact mul_le_mul_of_nonneg_right (norm_G_le_cap hi chi) (by positivity)
    _ = (gaussCap q / (q.totient : ℝ)) *
        (∑ chi : Character q, ∑ rho ∈ values chi, (analyticOrderNatAt chi.LFunction rho : ℝ)) * B := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (div_nonneg hg hp.le)) hB

theorem norm_closePacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) (positive : Bool)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => closeValues chi N positive) N eta‖ ≤
      gaussCap q / (q.totient : ℝ) * 7 * lowKernel N q := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  exact norm_packet_le_cap_count hi _ (by unfold lowKernel; positivity)
    (fun _ _ hr => Jrho_close hN hr he) (close_count hN hq positive)

theorem norm_middlePacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) (positive : Bool)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => middleValues chi N positive) N eta‖ ≤
      gaussCap q / (q.totient : ℝ) * 14000 * (innerWeight N * lowKernel N q) := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  exact norm_packet_le_cap_count hi _ (by unfold innerWeight lowKernel; positivity)
    (fun _ _ hr => Jrho_middle hN hr he) (middle_count hN hq positive)

theorem norm_leftPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => leftValues chi N positive) N eta‖ ≤
      outerWeight N * lowKernel N q * sharpGaussMass q a (lowHeight N q) := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  apply (norm_realPacketOn_le_weighted _ (fun _ _ hr => Jrho_left hN hr he)).trans
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        (sharpCount chi (lowHeight N q) * (outerWeight N * lowKernel N q)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (left_count_sharp hN chi positive)
        (by unfold outerWeight lowKernel; positivity)) (norm_nonneg _)
    _ = _ := by unfold sharpGaussMass; simp only [← mul_assoc, ← Finset.sum_mul]; ring

theorem largeLowPacket_eq_three {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    realPacketOn q a (fun chi => largeLowValues chi N positive) N eta =
      realPacketOn q a (fun chi => closeValues chi N positive) N eta +
        realPacketOn q a (fun chi => middleValues chi N positive) N eta +
          realPacketOn q a (fun chi => leftValues chi N positive) N eta := by
  unfold realPacketOn closeValues middleValues leftValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hi : realAlpha N ≤ rho.re <;> by_cases ho : outerAlpha N ≤ rho.re <;>
    simp [hi, ho, not_le.mp, not_lt.mpr]

theorem norm_largeLowPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceP N) (hi : sourceIndex a q) (positive : Bool)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => largeLowValues chi N positive) N eta‖ ≤ packetFee N a q := by
  rw [largeLowPacket_eq_three]
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans (add_le_add
    (norm_closePacket hN hq hi positive he) (norm_middlePacket hN hq hi positive he)))
    (norm_leftPacket hN positive he)).trans_eq
  unfold packetFee
  ring

theorem restPacket_eq_largeLow_add_high {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    realPacketOn q a (fun chi => restValues chi N positive) N eta =
      realPacketOn q a (fun chi => largeLowValues chi N positive) N eta +
        realPacketOn q a (fun chi => highValues chi N positive) N eta := by
  simpa only [largeLowValues, highValues, not_le] using
    realPacketOn_split a N eta (fun chi => restValues chi N positive)
      (fun rho => |rho.im| ≤ lowHeight N q)

theorem cap_ratio_le_one {q : ℕ} [NeZero q] :
    gaussCap q / (q.totient : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact (div_le_one hp).mpr (min_le_right _ _)

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining
