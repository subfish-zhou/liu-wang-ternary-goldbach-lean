import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.LowPacket

/-! 下半实部保留 q·height 的抵消及 Gauss 平均，付清低高度族而不留下实部缺口。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters CompleteExpansion CharacterExpansion ArcGeometry

theorem lowerLow_count_sharp {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    (∑ rho ∈ lowerLowValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      sharpCount chi (max 10000 (lowHeight N q)) := by
  apply le_trans _ (complete_count_le_sharp chi
    ((by norm_num : (0 : ℝ) ≤ 10000).trans (le_max_left _ _)))
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
  intro rho hr
  have hh := mem_zeroValues.mp (low_subset_zero chi positive (Finset.mem_filter.mp hr).1)
  exact mem_zeroValues.mpr ⟨hh.1, hh.2.1, hh.2.2.1,
    hh.2.2.2.1.trans (le_max_right _ _), hh.2.2.2.2⟩

theorem q_sharp_low_count {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ realModulusLimit N) (chi : Character q) :
    (q : ℝ) * sharpCount chi (max 10000 (lowHeight N q)) ≤
      (3 / 10 : ℝ) * sourceL N ^ 3 * Real.log (sourceL N) := by
  let y := max 10000 (lowHeight N q)
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hl : 0 ≤ Real.log (sourceL N) := Real.log_nonneg
    (one_le_sourceL (exp_2000_le_of_exp_3100_le hN))
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hy : (10000 : ℝ) ≤ y := le_max_left _ _
  have hp := low_height_product hN hq
  change (q : ℝ) * y ≤ sourceL N ^ 3 / 100 at hp
  have hlog : Real.log ((q : ℝ) * y) ≤ 3 * Real.log (sourceL N) := by
    have hh : (q : ℝ) * y ≤ sourceL N ^ 3 := by nlinarith [pow_nonneg hL.le 3]
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (mul_pos hq0 (by linarith : 0 < y)) hh
  calc
    _ ≤ (q : ℝ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      mul_le_mul_of_nonneg_left (sharpCount_le_ten chi hy) hq0.le
    _ = 10 * ((q : ℝ) * y) * Real.log ((q : ℝ) * y) := by ring
    _ ≤ 10 * (sourceL N ^ 3 / 100) * (3 * Real.log (sourceL N)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hlog
        (Real.log_nonneg (by nlinarith)) (by positivity)
    _ = _ := by ring

theorem Jrho_lowerLow {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ lowerLowValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ 9 * (q : ℝ) * (N : ℝ) / sourceL N ^ 6 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
  apply (Jrho_low_weight hN hr he).trans
  calc
    _ ≤ (1 / sourceL N ^ 3) * (9 * (q : ℝ) * (N : ℝ) / sourceL N ^ 3) :=
      mul_le_mul_of_nonneg_right (left_low_weight hN hb.le) (by positivity)
    _ = _ := by field_simp

theorem norm_lowerLowPacket_sharp {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => lowerLowValues chi N positive) N eta‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        (sharpCount chi (max 10000 (lowHeight N q)) *
          (9 * (q : ℝ) * (N : ℝ) / sourceL N ^ 6)) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply (norm_realPacketOn_le_weighted _ (fun _ _ hr => Jrho_lowerLow hN hr he)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro chi _
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (lowerLow_count_sharp chi positive) (by positivity)) (norm_nonneg _)

theorem norm_lowerLowPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => lowerLowValues chi N positive) N eta‖ ≤
      (27 / 200 : ℝ) * (N : ℝ) * Real.log (sourceL N) / sourceL N ^ 2 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hl : 0 ≤ Real.log (sourceL N) := Real.log_nonneg
    (one_le_sourceL (exp_2000_le_of_exp_3100_le hN))
  by_cases hq : (q : ℝ) ≤ realModulusLimit N
  · have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N / 20 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · positivity
      · have hh : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
        unfold realModulusLimit at hq
        nlinarith
    have hc (chi : Character q) :
        ‖∑ rho ∈ lowerLowValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
        (27 / 10 : ℝ) * (N : ℝ) * Real.log (sourceL N) / sourceL N ^ 3 := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ rho ∈ lowerLowValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ) *
            (9 * (q : ℝ) * (N : ℝ) / sourceL N ^ 6) := by
          apply Finset.sum_le_sum
          intro rho hr
          rw [norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (Jrho_lowerLow hN hr he) (Nat.cast_nonneg _)
        _ = ((q : ℝ) * ∑ rho ∈ lowerLowValues chi N positive,
            (analyticOrderNatAt chi.LFunction rho : ℝ)) * (9 * (N : ℝ) / sourceL N ^ 6) := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ ((3 / 10 : ℝ) * sourceL N ^ 3 * Real.log (sourceL N)) *
            (9 * (N : ℝ) / sourceL N ^ 6) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact (mul_le_mul_of_nonneg_left (lowerLow_count_sharp chi positive)
            (Nat.cast_nonneg q)).trans (q_sharp_low_count hN hq chi)
        _ = _ := by field_simp; ring
    apply (norm_gauss_packet_le a _ (by positivity) hc).trans
    calc
      _ ≤ (sourceL N / 20) * ((27 / 10 : ℝ) * (N : ℝ) * Real.log (sourceL N) / sourceL N ^ 3) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by field_simp; ring
  · have hz : realPacketOn q a (fun chi => lowerLowValues chi N positive) N eta = 0 := by
      simp [realPacketOn, lowerLowValues, lowValues, hq]
    rw [hz, norm_zero]
    positivity

def lowFee (N : ℕ) : ℝ :=
  (63 / 400 : ℝ) * (N : ℝ) / sourceL N +
    (27 / 200 : ℝ) * (N : ℝ) * Real.log (sourceL N) / sourceL N ^ 2

theorem afterRealPacket_eq_low_add_rest {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    realPacketOn q a (fun chi => afterRealValues chi N positive) N eta =
      realPacketOn q a (fun chi => lowValues chi N positive) N eta +
        realPacketOn q a (fun chi => restValues chi N positive) N eta :=
  realPacketOn_split a N eta (fun chi => afterRealValues chi N positive)
    (fun rho => (q : ℝ) ≤ realModulusLimit N ∧ |rho.im| ≤ lowHeight N q)

theorem norm_lowPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => lowValues chi N positive) N eta‖ ≤ lowFee N := by
  have hs : realPacketOn q a (fun chi => lowValues chi N positive) N eta =
      realPacketOn q a (fun chi => upperLowValues chi N positive) N eta +
        realPacketOn q a (fun chi => lowerLowValues chi N positive) N eta := by
    simpa only [upperLowValues, lowerLowValues, not_le] using
      realPacketOn_split a N eta (fun chi => lowValues chi N positive)
        (fun rho => realAlpha N ≤ rho.re)
  rw [hs]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_upperLowPacket hN positive he) (norm_lowerLowPacket hN positive he)).trans_eq
  unfold lowFee
  ring

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
