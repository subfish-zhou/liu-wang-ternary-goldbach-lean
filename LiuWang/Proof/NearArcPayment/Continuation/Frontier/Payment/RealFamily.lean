import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Integral

/-! 对 q≤L 的实际近一实零族付款，包括 principal 和例外零；不使用无零区删除。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment

open Interfaces Parameters CompleteExpansion CharacterExpansion NearOneDensity ArcGeometry

def realScale (N : ℕ) : ℝ := sourceL N ^ 4

def realAlpha (N : ℕ) : ℝ := 1 - 0.27 / Real.log (realScale N)

def realValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (residualValues chi N positive).filter (fun rho =>
    (q : ℝ) ≤ sourceL N ∧ rho.im = 0 ∧ realAlpha N ≤ rho.re)

def lastValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (residualValues chi N positive).filter (fun rho =>
    ¬ ((q : ℝ) ≤ sourceL N ∧ rho.im = 0 ∧ realAlpha N ≤ rho.re))

def realPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ realValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def lastPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ lastValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem residualPacket_eq_real_add_last {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    residualPacket q N a positive eta =
      realPacket q N a positive eta + lastPacket q N a positive eta := by
  unfold residualPacket realPacket lastPacket realValues lastValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hh : (q : ℝ) ≤ sourceL N ∧ rho.im = 0 ∧ realAlpha N ≤ rho.re <;> simp [hh]

theorem real_domain {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ sourceL N) :
    100000000000 ≤ realScale N ∧ (q : ℝ) * max 1 (0 : ℝ) ≤ realScale N := by
  have hL := sourceL_pos hN
  have hl : (1 : ℝ) ≤ sourceL N ^ 3 := one_le_pow₀ (one_le_sourceL hN)
  have hh : sourceL N ≤ sourceL N ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hl hL.le,
      show sourceL N * sourceL N ^ 3 = sourceL N ^ 4 by ring]
  constructor
  · exact (by norm_num : (100000000000 : ℝ) ≤ 2000 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 4)
  · simpa only [realScale, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), mul_one] using hq.trans hh

theorem real_count_le_row {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (positive : Bool) :
    (∑ chi : Character q, ∑ rho ∈ realValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
  by_cases hq : (q : ℝ) ≤ sourceL N
  · obtain ⟨hz, hqy⟩ := real_domain hN hq
    have hr := NearOneDensity.Continuation.complete_tail_count_row .r027 hz hqy
      (alpha := realAlpha N) (by rfl)
    have hc : (∑ chi : Character q,
        ∑ rho ∈ (CompleteExpansion.zeroValues chi 0).filter (fun rho => realAlpha N ≤ rho.re),
          (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
      norm_num [rowBound, rowMultiplicity, rowSelectedBound] at hr
      exact_mod_cast hr
    apply le_trans _ hc
    apply Finset.sum_le_sum
    intro chi _
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
    intro rho hr
    obtain ⟨hr, _, hg, ha⟩ := Finset.mem_filter.mp hr
    have ht := (Finset.mem_filter.mp hr).1
    have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
    obtain ⟨hz, h0, h1, _, hb, _⟩ := (finalValues_literal chi).mp hf
    exact Finset.mem_filter.mpr ⟨mem_zeroValues.mpr
      ⟨hz, h0, h1, by simp [hg], by linarith⟩, ha⟩
  · simp [realValues, hq]

theorem reciprocal_same_q {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    1 / (Real.pi * |eta|) ≤ 3 * (q : ℝ) * (N : ℝ) / sourceP N := by
  have hp := sourceP_pos hN
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hn := natCast_pos_of_exp_le hN
  calc
    _ ≤ 1 / (Real.pi * deltaRadius N q) :=
      one_div_le_one_div_of_le
        (mul_pos Real.pi_pos (deltaRadius_pos hN (NeZero.pos q)))
        (mul_le_mul_of_nonneg_left he.le Real.pi_pos.le)
    _ = (10 / 3.36) * (q : ℝ) * (N : ℝ) / sourceP N := by
      unfold deltaRadius
      field_simp
    _ ≤ _ := by gcongr; norm_num

theorem Jrho_real_family {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ} {positive : Bool}
    (hr : rho ∈ realValues chi N positive) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ 3 * (N : ℝ) / sourceL N ^ 2 := by
  have hL := sourceL_pos hN
  have hP := sourceP_pos hN
  obtain ⟨hr, hq, hg, _⟩ := Finset.mem_filter.mp hr
  have ht := (Finset.mem_filter.mp hr).1
  have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hb := ((finalValues_literal chi).mp hf).2.2.1.le
  have he0 : eta ≠ 0 :=
    abs_pos.mp ((deltaRadius_pos hN (NeZero.pos q)).trans he)
  have hw : (0.001 * (N : ℝ)) ^ (rho.re - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (sourceWindow_gt_one hN).le (sub_nonpos.mpr hb)
  calc
    _ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|) :=
      OscillatoryBounds.Jrho_real_reciprocal (nat_pos_of_exp_le hN) hb hg he0
    _ ≤ 1 / (Real.pi * |eta|) :=
      div_le_div_of_nonneg_right hw (mul_nonneg Real.pi_pos.le (abs_nonneg _))
    _ ≤ 3 * (q : ℝ) * (N : ℝ) / sourceP N := reciprocal_same_q hN he
    _ ≤ 3 * sourceL N * (N : ℝ) / sourceP N := by gcongr
    _ = _ := by unfold sourceP; field_simp

theorem norm_realPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (positive : Bool) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖realPacket q N a positive eta‖ ≤ 21 * (N : ℝ) / sourceL N ^ 2 := by
  have hL := sourceL_pos hN
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hc (chi : Character q) :
      ‖∑ rho ∈ realValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (∑ rho ∈ realValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
        (3 * (N : ℝ) / sourceL N ^ 2) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro rho hr
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (Jrho_real_family hN hr he) (Nat.cast_nonneg _)
  unfold realPacket
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, (q.totient : ℝ) *
        ((∑ rho ∈ realValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
          (3 * (N : ℝ) / sourceL N ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul (norm_G_le_totient a chi) (hc chi) (norm_nonneg _) (Nat.cast_nonneg _)
    _ = (∑ chi : Character q, ∑ rho ∈ realValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℝ)) * (3 * (N : ℝ) / sourceL N ^ 2) := by
      rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul, ← Finset.sum_mul]
    _ ≤ 7 * (3 * (N : ℝ) / sourceL N ^ 2) :=
      mul_le_mul_of_nonneg_right (real_count_le_row hN positive) (by positivity)
    _ = _ := by ring

theorem norm_realPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (positive : Bool) {eta : ℝ}
    (he : deltaRadius N q < |eta|) :
    ‖realPacket q N a positive eta‖ ≤ 0.007 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hp : (21 : ℝ) ≤ 0.007 * sourceL N := by linarith [sourceL_ge_3100 hN]
  apply (norm_realPacket_le_polynomial hN0 positive he).trans
  rw [pow_two, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ hL).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment
