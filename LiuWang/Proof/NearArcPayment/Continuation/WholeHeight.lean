import LiuWang.Proof.NearArcPayment.Continuation.Integral

/-!
# A moving all-height payment inside the remaining packet

The full-height coarse count also pays a moving strip beyond beta = 3/4.
The filter is taken inside unpaidValues, so neither earlier payment is
charged again. No density estimate or zero-free assertion is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion

def wholeCutoff (N : ℕ) : ℝ :=
  1 - 24 * Real.log (sourceL N) / sourceL N

def wholePaidValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (unpaidValues chi N).filter (fun rho => rho.re ≤ wholeCutoff N)

def finalValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (unpaidValues chi N).filter (fun rho => wholeCutoff N < rho.re)

def wholePaidPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ wholePaidValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def finalPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ finalValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem unpaidPacket_eq_whole_add_final {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    unpaidPacket q N a eta = wholePaidPacket q N a eta + finalPacket q N a eta := by
  unfold unpaidPacket wholePaidPacket finalPacket wholePaidValues finalValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hb : rho.re ≤ wholeCutoff N <;> simp [hb]

theorem whole_weight_le_log_power {N : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) {beta : ℝ} (hb : beta ≤ wholeCutoff N) :
    (N : ℝ) ^ (beta - 1) ≤ 1 / sourceL N ^ 24 := by
  have hn := natCast_pos_of_exp_le hN
  have hL := sourceL_pos hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have heq :
      (N : ℝ) ^ (-(24 * Real.log (sourceL N) / sourceL N)) =
        1 / sourceL N ^ 24 := by
    rw [Real.rpow_def_of_pos hn]
    change Real.exp (sourceL N * -(24 * Real.log (sourceL N) / sourceL N)) = _
    rw [show sourceL N * -(24 * Real.log (sourceL N) / sourceL N) =
      -(24 * Real.log (sourceL N)) by field_simp]
    rw [Real.exp_neg, show (24 : ℝ) * Real.log (sourceL N) =
      Real.log (sourceL N ^ 24) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hL 24)]
    simp only [one_div]
  rw [← heq]
  apply Real.rpow_le_rpow_of_exponent_le hn1
  unfold wholeCutoff at hb
  linarith

theorem Jrho_wholePaid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    (hr : rho ∈ wholePaidValues chi N) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤ 2 * (N : ℝ) / sourceL N ^ 24 := by
  have hn := natCast_pos_of_exp_le hN
  obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
  have hr0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hb0 : 1 / 2 ≤ rho.re := (mem_zeroValues.mp hr0).2.2.2.2
  have hc : (1 - (0.001 : ℝ) ^ rho.re) / rho.re ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < rho.re)).mpr
    linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0.001) rho.re]
  have heq : (N : ℝ) ^ rho.re = (N : ℝ) * (N : ℝ) ^ (rho.re - 1) := by
    conv_rhs => lhs; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ (1 - (0.001 : ℝ) ^ rho.re) / rho.re * (N : ℝ) ^ rho.re :=
      OscillatoryBounds.Jrho_weight (nat_pos_of_exp_le hN) (by linarith) eta
    _ ≤ 2 * (N : ℝ) ^ rho.re :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn.le _)
    _ = 2 * ((N : ℝ) * (N : ℝ) ^ (rho.re - 1)) := by rw [heq]
    _ ≤ 2 * ((N : ℝ) * (1 / sourceL N ^ 24)) := by
      gcongr
      exact whole_weight_le_log_power hN hb
    _ = _ := by ring

theorem wholePaid_count_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    (∑ rho ∈ wholePaidValues chi N, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      180 * sourceL N ^ 16 := by
  have hL := sourceL_pos hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hT := sourceT_pos hN
  have hT0 : 10000 ≤ sourceT N :=
    (by norm_num : (10000 : ℝ) ≤ 2000 ^ 15).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 15)
  have hs : wholePaidValues chi N ⊆ zeroValues chi (sourceT N) := by
    intro rho hr
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_filter.mp hr).1).1).1
  have hh : Real.log ((q : ℝ) * sourceT N) ≤ 18 * sourceL N := by
    calc
      _ ≤ Real.log (sourceL N ^ 18) := by
        apply Real.log_le_log (mul_pos hq0 hT)
        have hp := mul_le_mul_of_nonneg_right hq hT.le
        simpa only [sourceP, sourceT, ← pow_add] using hp
      _ = 18 * Real.log (sourceL N) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos hL]
  calc
    _ ≤ ∑ rho ∈ zeroValues chi (sourceT N), (analyticOrderNatAt chi.LFunction rho : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ 10 * sourceT N * Real.log ((q : ℝ) * sourceT N) := count_complete_le chi hT0
    _ ≤ 10 * sourceT N * (18 * sourceL N) := by gcongr
    _ = _ := by unfold sourceT; ring

theorem norm_wholePaidPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    ‖wholePaidPacket q N a eta‖ ≤ 360 * (N : ℝ) / sourceL N ^ 5 := by
  have hL := sourceL_pos hN
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N ^ 3 := by
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
    exact (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q :
      (q.totient : ℝ) ≤ (q : ℝ))).trans (hsq.trans hq)
  have hchar (chi : Character q) :
      ‖∑ rho ∈ wholePaidValues chi N,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (180 * sourceL N ^ 16) * (2 * (N : ℝ) / sourceL N ^ 24) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ rho ∈ wholePaidValues chi N, (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (2 * (N : ℝ) / sourceL N ^ 24) := by
        apply Finset.sum_le_sum
        intro rho hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (Jrho_wholePaid hN hr eta) (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (wholePaid_count_le hN hq chi) (by positivity)
  apply (norm_gauss_packet_le a _ (by positivity) hchar).trans
  calc
    _ ≤ sourceL N ^ 3 * ((180 * sourceL N ^ 16) * (2 * (N : ℝ) / sourceL N ^ 24)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp; ring

theorem norm_wholePaidPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (eta : ℝ) :
    ‖wholePaidPacket q N a eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hp : (3600000 : ℝ) ≤ sourceL N ^ 4 :=
    (by norm_num : (3600000 : ℝ) ≤ 3100 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 4)
  apply (norm_wholePaidPacket_le_polynomial hN0 hq eta).trans
  rw [show sourceL N ^ 5 = sourceL N ^ 4 * sourceL N by ring, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ (pow_pos hL 4)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation
