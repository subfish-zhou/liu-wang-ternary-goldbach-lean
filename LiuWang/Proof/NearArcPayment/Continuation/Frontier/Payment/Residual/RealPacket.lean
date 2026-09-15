import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Estimates

/-! 支付 q≤L²/400 的整个剩余实零族。内部实部分割只用于两种母界，最终不留实部缺口。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters CompleteExpansion CharacterExpansion NearOneDensity ArcGeometry

def allRealValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (lastValues chi N positive).filter (fun rho => (q : ℝ) ≤ realModulusLimit N ∧ rho.im = 0)

def afterRealValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (lastValues chi N positive).filter (fun rho => ¬ ((q : ℝ) ≤ realModulusLimit N ∧ rho.im = 0))

def upperRealValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (allRealValues chi N positive).filter (fun rho => realAlpha N ≤ rho.re)

def lowerRealValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (allRealValues chi N positive).filter (fun rho => rho.re < realAlpha N)

def realPacketOn (q : ℕ) [NeZero q] (a : ℕ) (values : Character q → Finset ℂ)
    (N : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ values chi, (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem realPacketOn_split {q : ℕ} [NeZero q] (a N : ℕ) (eta : ℝ)
    (values : Character q → Finset ℂ) (p : ℂ → Prop) [DecidablePred p] :
    realPacketOn q a values N eta =
      realPacketOn q a (fun chi => (values chi).filter p) N eta +
        realPacketOn q a (fun chi => (values chi).filter (fun rho => ¬ p rho)) N eta := by
  unfold realPacketOn
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hh : p rho <;> simp [hh]

theorem lastPacket_eq_real_add_after {q : ℕ} [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) :
    lastPacket q N a positive eta =
      realPacketOn q a (fun chi => allRealValues chi N positive) N eta +
        realPacketOn q a (fun chi => afterRealValues chi N positive) N eta :=
  realPacketOn_split a N eta (fun chi => lastValues chi N positive)
    (fun rho => (q : ℝ) ≤ realModulusLimit N ∧ rho.im = 0)

theorem allRealPacket_eq_upper_add_lower {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    realPacketOn q a (fun chi => allRealValues chi N positive) N eta =
      realPacketOn q a (fun chi => upperRealValues chi N positive) N eta +
        realPacketOn q a (fun chi => lowerRealValues chi N positive) N eta := by
  simpa only [upperRealValues, lowerRealValues, not_le] using
    realPacketOn_split a N eta (fun chi => allRealValues chi N positive)
      (fun rho => realAlpha N ≤ rho.re)

theorem allReal_subset_zero {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    allRealValues chi N positive ⊆ zeroValues chi 0 := by
  intro rho hr
  obtain ⟨hr, _, hg⟩ := Finset.mem_filter.mp hr
  have ht := ((lastValues_exact chi positive).mp hr).1
  have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  obtain ⟨hz, h0, h1, _, hb, _⟩ := (finalValues_literal chi).mp hf
  exact mem_zeroValues.mpr ⟨hz, h0, h1, by simp [hg], by linarith⟩

theorem upperReal_count {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) :
    (∑ chi : Character q, ∑ rho ∈ upperRealValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
  by_cases hq : (q : ℝ) ≤ realModulusLimit N
  · obtain ⟨hz, hqy⟩ := real_modulus_domain hN hq
    have hh := NearOneDensity.Continuation.complete_tail_count_row .r027 hz hqy
      (alpha := realAlpha N) (by rfl)
    have hc : (∑ chi : Character q,
        ∑ rho ∈ (CompleteExpansion.zeroValues chi 0).filter (fun rho => realAlpha N ≤ rho.re),
          (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
      norm_num [rowBound, rowMultiplicity, rowSelectedBound] at hh
      exact_mod_cast hh
    apply le_trans _ hc
    apply Finset.sum_le_sum
    intro chi _
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
    intro rho hr
    obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨allReal_subset_zero chi positive hr, hb⟩
  · simp [upperRealValues, allRealValues, hq]

theorem lowerReal_count_sharp {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    (∑ rho ∈ lowerRealValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      sharpCount chi 0 :=
  (Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans (allReal_subset_zero chi positive))
    (fun _ _ _ => Nat.cast_nonneg _)).trans (complete_count_le_sharp chi (by norm_num))

theorem Jrho_allReal_upper {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ allRealValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ 3 * (N : ℝ) / (400 * sourceL N) := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hP := sourceP_pos hN0
  have hb := (mem_zeroValues.mp (allReal_subset_zero chi positive hr)).2.2.1.le
  obtain ⟨_, hq, hg⟩ := Finset.mem_filter.mp hr
  have he0 : eta ≠ 0 := abs_pos.mp ((deltaRadius_pos hN0 (NeZero.pos q)).trans he)
  have hw : (0.001 * (N : ℝ)) ^ (rho.re - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (sourceWindow_gt_one hN0).le (sub_nonpos.mpr hb)
  calc
    _ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|) :=
      OscillatoryBounds.Jrho_real_reciprocal (nat_pos_of_exp_le hN) hb hg he0
    _ ≤ 1 / (Real.pi * |eta|) :=
      div_le_div_of_nonneg_right hw (mul_nonneg Real.pi_pos.le (abs_nonneg _))
    _ ≤ 3 * (q : ℝ) * (N : ℝ) / sourceP N := reciprocal_same_q hN0 he
    _ ≤ 3 * realModulusLimit N * (N : ℝ) / sourceP N := by gcongr
    _ = _ := by unfold realModulusLimit sourceP; field_simp

theorem Jrho_allReal_lower {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ lowerRealValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ 3 * (N : ℝ) / (400 * sourceL N ^ 3) := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hP := sourceP_pos hN0
  obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hr
  have hb := (mem_zeroValues.mp (allReal_subset_zero chi positive hr)).2.2.1.le
  obtain ⟨_, hq, hg⟩ := Finset.mem_filter.mp hr
  have he0 : eta ≠ 0 := abs_pos.mp ((deltaRadius_pos hN0 (NeZero.pos q)).trans he)
  calc
    _ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|) :=
      OscillatoryBounds.Jrho_real_reciprocal (nat_pos_of_exp_le hN) hb hg he0
    _ = (0.001 * (N : ℝ)) ^ (rho.re - 1) * (1 / (Real.pi * |eta|)) := by ring
    _ ≤ (1 / sourceL N ^ 2) * (3 * (q : ℝ) * (N : ℝ) / sourceP N) :=
      mul_le_mul (left_real_weight hN ha.le) (reciprocal_same_q hN0 he)
        (by positivity) (by positivity)
    _ ≤ (1 / sourceL N ^ 2) * (3 * realModulusLimit N * (N : ℝ) / sourceP N) := by gcongr
    _ = _ := by unfold realModulusLimit sourceP; field_simp

theorem norm_realPacketOn_le_weighted {N a q : ℕ} [NeZero q]
    (values : Character q → Finset ℂ) {eta B : ℝ}
    (hb : ∀ chi rho, rho ∈ values chi → ‖Jrho N rho eta‖ ≤ B) :
    ‖realPacketOn q a values N eta‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        ((∑ rho ∈ values chi, (analyticOrderNatAt chi.LFunction rho : ℝ)) * B) := by
  unfold realPacketOn
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro rho hr
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hb chi rho hr) (Nat.cast_nonneg _)

theorem norm_upperRealPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => upperRealValues chi N positive) N eta‖ ≤
      21 * (N : ℝ) / (400 * sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  apply (norm_realPacketOn_le_weighted _ (fun _ _ hr =>
    Jrho_allReal_upper hN (Finset.mem_filter.mp hr).1 he)).trans
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, (q.totient : ℝ) *
        ((∑ rho ∈ upperRealValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
          (3 * (N : ℝ) / (400 * sourceL N))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      exact mul_le_mul_of_nonneg_right (norm_G_le_totient a chi) (by positivity)
    _ = (∑ chi : Character q, ∑ rho ∈ upperRealValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℝ)) * (3 * (N : ℝ) / (400 * sourceL N)) := by
      rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul, ← Finset.sum_mul]
    _ ≤ 7 * (3 * (N : ℝ) / (400 * sourceL N)) :=
      mul_le_mul_of_nonneg_right (upperReal_count hN positive) (by positivity)
    _ = _ := by ring

theorem norm_lowerRealPacket_sharp {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => lowerRealValues chi N positive) N eta‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        (sharpCount chi 0 * (3 * (N : ℝ) / (400 * sourceL N ^ 3))) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  apply (norm_realPacketOn_le_weighted _ (fun _ _ hr => Jrho_allReal_lower hN hr he)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro chi _
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (lowerReal_count_sharp chi positive) (by positivity)) (norm_nonneg _)

theorem norm_lowerRealPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => lowerRealValues chi N positive) N eta‖ ≤
      3 * (N : ℝ) / (8000 * sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  by_cases hq : (q : ℝ) ≤ realModulusLimit N
  · have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N / 20 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · positivity
      · have hh : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
        unfold realModulusLimit at hq
        nlinarith
    have hc (chi : Character q) :
        ‖∑ rho ∈ lowerRealValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
        sourceL N * (3 * (N : ℝ) / (400 * sourceL N ^ 3)) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ rho ∈ lowerRealValues chi N positive,
            (analyticOrderNatAt chi.LFunction rho : ℝ) * (3 * (N : ℝ) / (400 * sourceL N ^ 3)) := by
          apply Finset.sum_le_sum
          intro rho hr
          rw [norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (Jrho_allReal_lower hN hr he) (Nat.cast_nonneg _)
        _ ≤ _ := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right
            ((lowerReal_count_sharp chi positive).trans (sharp_zero_height hN hq chi)) (by positivity)
    apply (norm_gauss_packet_le a _ (by positivity) hc).trans
    calc
      _ ≤ (sourceL N / 20) * (sourceL N * (3 * (N : ℝ) / (400 * sourceL N ^ 3))) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by field_simp; ring
  · have hz : realPacketOn q a (fun chi => lowerRealValues chi N positive) N eta = 0 := by
      simp [realPacketOn, lowerRealValues, allRealValues, hq]
    rw [hz, norm_zero]
    positivity

theorem norm_allRealPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => allRealValues chi N positive) N eta‖ ≤
      (423 / 8000 : ℝ) * (N : ℝ) / sourceL N := by
  rw [allRealPacket_eq_upper_add_lower]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_upperRealPacket hN positive he) (norm_lowerRealPacket hN positive he)).trans_eq
  ring

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
