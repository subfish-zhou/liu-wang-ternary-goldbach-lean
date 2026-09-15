import LiuWang.Proof.NearArcPayment.Continuation.RightCost

/-!
# Paying a moving real-zero band by the reciprocal oscillatory kernel

The height-zero count is obtained by inclusion in the frozen height-10000
count, not by a density estimate. The cutoff is an explicit real-part filter
on the actual right-strip zeros, not a zero-free assertion.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion

def realCutoff (N : ℕ) : ℝ :=
  1 - 10 * Real.log (sourceL N) / Real.log (0.001 * (N : ℝ))

def realPaidValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (rightValues chi N).filter (fun rho => rho.im = 0 ∧ rho.re ≤ realCutoff N)

def residualValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (rightValues chi N).filter (fun rho => ¬ (rho.im = 0 ∧ rho.re ≤ realCutoff N))

def realPaidPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ realPaidValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def residualPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ residualValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem rightPacket_eq_paid_add_residual {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    rightPacket q N a eta = realPaidPacket q N a eta + residualPacket q N a eta := by
  unfold rightPacket realPaidPacket residualPacket realPaidValues residualValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : rho.im = 0 ∧ rho.re ≤ realCutoff N <;> simp [h]

theorem sourceWindow_gt_one {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) :
    1 < 0.001 * (N : ℝ) := by
  have ht : 1 ≤ sourceT N := one_le_pow₀ (one_le_sourceL hN)
  have hw := sourceT_lt_windowLower hN
  unfold sourceWindowLower at hw
  linarith

theorem real_weight_le_log_power {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {beta : ℝ} (hb : beta ≤ realCutoff N) :
    (0.001 * (N : ℝ)) ^ (beta - 1) ≤ 1 / sourceL N ^ 10 := by
  have hL := sourceL_pos hN
  have hw := sourceWindow_gt_one hN
  have hlw : 0 < Real.log (0.001 * (N : ℝ)) := Real.log_pos hw
  have heq :
      (0.001 * (N : ℝ)) ^ (-(10 * Real.log (sourceL N) /
        Real.log (0.001 * (N : ℝ)))) = 1 / sourceL N ^ 10 := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < 0.001 * (N : ℝ))]
    rw [show Real.log (0.001 * (N : ℝ)) *
        -(10 * Real.log (sourceL N) / Real.log (0.001 * (N : ℝ))) =
        -(10 * Real.log (sourceL N)) by field_simp]
    rw [Real.exp_neg, show (10 : ℝ) * Real.log (sourceL N) =
      Real.log (sourceL N ^ 10) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hL 10)]
    simp only [one_div]
  rw [← heq]
  apply Real.rpow_le_rpow_of_exponent_le hw.le
  unfold realCutoff at hb
  linarith

theorem reciprocal_on_M2 {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq0 : 0 < q)
    (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    1 / (Real.pi * |eta|) ≤ 3 * (N : ℝ) := by
  have hp := sourceP_pos hN
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
  have hn := natCast_pos_of_exp_le hN
  have hd := deltaRadius_pos hN hq0
  calc
    _ ≤ 1 / (Real.pi * deltaRadius N q) :=
      one_div_le_one_div_of_le (mul_pos Real.pi_pos hd)
        (mul_le_mul_of_nonneg_left he.le Real.pi_pos.le)
    _ = (10 / 3.36) * (q : ℝ) * (N : ℝ) / sourceP N := by
      unfold deltaRadius
      field_simp
    _ ≤ (10 / 3.36) * sourceP N * (N : ℝ) / sourceP N := by gcongr
    _ = (10 / 3.36) * (N : ℝ) := by field_simp
    _ ≤ _ := by gcongr; norm_num

theorem Jrho_real_paid {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq0 : 0 < q)
    (hq : (q : ℝ) ≤ sourceP N) {eta : ℝ} (he : deltaRadius N q < |eta|)
    {rho : ℂ} (hb1 : rho.re ≤ 1) (hreal : rho.im = 0)
    (hb : rho.re ≤ realCutoff N) :
    ‖Jrho N rho eta‖ ≤ 3 * (N : ℝ) / sourceL N ^ 10 := by
  have hL := sourceL_pos hN
  have he0 : eta ≠ 0 := abs_pos.mp ((deltaRadius_pos hN hq0).trans he)
  calc
    _ ≤ (0.001 * (N : ℝ)) ^ (rho.re - 1) / (Real.pi * |eta|) :=
      OscillatoryBounds.Jrho_real_reciprocal (nat_pos_of_exp_le hN) hb1 hreal he0
    _ = (0.001 * (N : ℝ)) ^ (rho.re - 1) * (1 / (Real.pi * |eta|)) := by ring
    _ ≤ (1 / sourceL N ^ 10) * (3 * (N : ℝ)) :=
      mul_le_mul (real_weight_le_log_power hN hb) (reciprocal_on_M2 hN hq0 hq he)
        (by positivity) (by positivity)
    _ = _ := by ring

theorem realPaidValues_subset_height {N q : ℕ} [NeZero q] (chi : Character q) :
    realPaidValues chi N ⊆ zeroValues chi 10000 := by
  intro rho hr
  obtain ⟨hr, hg, _⟩ := Finset.mem_filter.mp hr
  obtain ⟨hr, _⟩ := Finset.mem_filter.mp hr
  obtain ⟨hz, h0, h1, _, hh⟩ := mem_zeroValues.mp hr
  exact mem_zeroValues.mpr ⟨hz, h0, h1, by simp [hg], hh⟩

theorem realPaid_count_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    (∑ rho ∈ realPaidValues chi N, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      700000 * sourceL N := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hlogq : Real.log q ≤ 3 * Real.log (sourceL N) := by
    have h := Real.log_le_log hq0 hq
    simpa only [sourceP, Real.log_pow, Nat.cast_ofNat] using h
  have hh : Real.log ((q : ℝ) * 10000) ≤ 7 * sourceL N := by
    rw [Real.log_mul hq0.ne' (by norm_num : (10000 : ℝ) ≠ 0)]
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10000)
    have hl := Real.log_le_sub_one_of_pos hL
    linarith [sourceL_ge_3100 hN]
  calc
    _ ≤ ∑ rho ∈ zeroValues chi 10000, (analyticOrderNatAt chi.LFunction rho : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (realPaidValues_subset_height chi)
        (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ 10 * 10000 * Real.log ((q : ℝ) * 10000) := count_complete_le chi le_rfl
    _ ≤ _ := by linarith

theorem norm_realPaidPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPaidPacket q N a eta‖ ≤ 2100000 * (N : ℝ) / sourceL N ^ 6 := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hq0 := NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq0
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq0)
  have hphi_q : Real.sqrt (q.totient : ℝ) ≤ sourceL N ^ 3 := by
    have hs : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
    exact (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q :
      (q.totient : ℝ) ≤ (q : ℝ))).trans (hs.trans hq)
  have hchar (chi : Character q) :
      ‖∑ rho ∈ realPaidValues chi N,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (700000 * sourceL N) * (3 * (N : ℝ) / sourceL N ^ 10) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ rho ∈ realPaidValues chi N,
          (analyticOrderNatAt chi.LFunction rho : ℝ) * (3 * (N : ℝ) / sourceL N ^ 10) := by
        apply Finset.sum_le_sum
        intro rho hr
        obtain ⟨hr, hg, hb⟩ := Finset.mem_filter.mp hr
        obtain ⟨hr, _⟩ := Finset.mem_filter.mp hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (Jrho_real_paid hN0 hq0 hq he (mem_zeroValues.mp hr).2.2.1.le hg hb)
          (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (realPaid_count_le hN hq chi) (by positivity)
  unfold realPaidPacket
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        ((700000 * sourceL N) * (3 * (N : ℝ) / sourceL N ^ 10)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hchar chi) (norm_nonneg _)
    _ = ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖) *
        ((700000 * sourceL N) * (3 * (N : ℝ) / sourceL N ^ 10)) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ sourceL N ^ 3 *
        ((700000 * sourceL N) * (3 * (N : ℝ) / sourceL N ^ 10)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (q.totient : ℝ)⁻¹ * (Real.sqrt (q.totient : ℝ) * (q.totient : ℝ)) :=
          mul_le_mul_of_nonneg_left (NonprincipalPacket.sum_norm_G_le a) (by positivity)
        _ = Real.sqrt (q.totient : ℝ) := by field_simp
        _ ≤ _ := hphi_q
    _ = _ := by field_simp; ring

theorem norm_realPaidPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPaidPacket q N a eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hp : (21000000000 : ℝ) ≤ sourceL N ^ 5 :=
    (by norm_num : (21000000000 : ℝ) ≤ 3100 ^ 5).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 5)
  apply (norm_realPaidPacket_le_polynomial hN hq he).trans
  rw [show sourceL N ^ 6 = sourceL N ^ 5 * sourceL N by ring, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ (pow_pos hL 5)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation
