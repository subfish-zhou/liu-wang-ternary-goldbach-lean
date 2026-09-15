import LiuWang.Proof.NearArcPayment.Continuation.Frontier.SameSign
import LiuWang.Proof.DirichletZeroCount.Remainder.UniformWeights

/-!
同号中高度带是真实 finalValues 的新子集。母界保留已接回的逐字符导子
锐计数与原 Gauss/phi 权；十倍包络只用于末端保守小数付款。
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier

open Interfaces Parameters CompleteExpansion CharacterExpansion
open DirichletZeroCount

def alignedCutoff (N : ℕ) : ℝ := 1 - 12 * Real.log (sourceL N) / sourceL N

def alignedValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (finalValues chi N).filter (fun rho =>
    sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧
      rho.re ≤ alignedCutoff N ∧ if positive then 0 < rho.im else rho.im < 0)

def remainingValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (finalValues chi N).filter (fun rho =>
    ¬ (sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧
      rho.re ≤ alignedCutoff N ∧ if positive then 0 < rho.im else rho.im < 0))

def alignedPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ alignedValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def remainingPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ remainingValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem finalPacket_eq_aligned_add_remaining {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    finalPacket q N a eta =
      alignedPacket q N a positive eta + remainingPacket q N a positive eta := by
  unfold finalPacket alignedPacket remainingPacket alignedValues remainingValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hh : sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧
      rho.re ≤ alignedCutoff N ∧ if positive then 0 < rho.im else rho.im < 0 <;> simp [hh]

def sharpCount {q : ℕ} (chi : Character q) (y : ℝ) : ℝ :=
  if chi = 1 then Remainder.uniformPrincipalBound y
  else Remainder.uniformNonprincipalBound chi.conductor (Remainder.parityShift chi) y

theorem complete_count_le_sharp {q : ℕ} [NeZero q] (chi : Character q)
    {y : ℝ} (hy : 0 ≤ y) :
    (∑ rho ∈ zeroValues chi y, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      sharpCount chi y := by
  rw [← Nat.cast_sum, ← Applications.count_half_eq_complete]
  unfold sharpCount
  split_ifs with hc
  · subst chi
    exact Remainder.count_principal_le_uniformBound q (by norm_num) hy
  · exact Remainder.count_nonprincipal_le_uniformBound hc (alpha := 1 / 2) (by norm_num) hy

theorem sharpCount_le_ten {q : ℕ} [NeZero q] (chi : Character q)
    {y : ℝ} (hy : 10000 ≤ y) :
    sharpCount chi y ≤ 10 * y * Real.log ((q : ℝ) * y) := by
  unfold sharpCount
  split_ifs
  · exact (min_le_left _ _).trans (Applications.principalBound_le_ten (q := q) hy)
  · apply (Remainder.uniformNonprincipalBound_mono
      (Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (BombieriVinogradov.DirichletCharacter.conductor_le_level chi) (by linarith)).trans
    exact (min_le_left _ _).trans (Applications.nonprincipalBound_le_ten hy)

theorem aligned_weight {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) {beta : ℝ}
    (hb : beta ≤ alignedCutoff N) :
    (N : ℝ) ^ beta ≤ (N : ℝ) / sourceL N ^ 12 := by
  have hn := natCast_pos_of_exp_le hN
  have hL := sourceL_pos hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have heq : (N : ℝ) ^ (alignedCutoff N) = (N : ℝ) / sourceL N ^ 12 := by
    unfold alignedCutoff
    rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_def_of_pos hn]
    change (N : ℝ) / Real.exp (sourceL N * (12 * Real.log (sourceL N) / sourceL N)) = _
    rw [show sourceL N * (12 * Real.log (sourceL N) / sourceL N) =
      12 * Real.log (sourceL N) by field_simp]
    rw [show (12 : ℝ) * Real.log (sourceL N) = Real.log (sourceL N ^ 12) by
      rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL 12)]
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hb).trans_eq heq

theorem aligned_subset_height {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    alignedValues chi N positive ⊆ zeroValues chi (sourceL N ^ 8) := by
  intro rho hr
  obtain ⟨hr, _, hu, _, _⟩ := Finset.mem_filter.mp hr
  obtain ⟨hz, h0, h1, _, hb, _⟩ := finalValues_literal chi |>.mp hr
  exact mem_zeroValues.mpr ⟨hz, h0, h1, hu, by linarith⟩

theorem Jrho_aligned {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    {positive : Bool} (hr : rho ∈ alignedValues chi N positive) {eta : ℝ}
    (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖Jrho N rho eta‖ ≤ (4000 * (N : ℝ) / sourceL N ^ 12) / |rho.im| := by
  obtain ⟨hf, hl, _, hb, hs⟩ := Finset.mem_filter.mp hr
  have hg : rho.im ≠ 0 := abs_pos.mp ((pow_pos (sourceL_pos hN) 4).trans_le hl)
  obtain ⟨_, h0, h1, _⟩ := (finalValues_literal chi).mp hf
  have hsign : 0 ≤ eta * rho.im := by
    cases positive
    · exact mul_nonneg_of_nonpos_of_nonpos he (le_of_lt hs)
    · exact mul_nonneg he (le_of_lt hs)
  apply (Jrho_sameSign (nat_pos_of_exp_le hN) h0.le h1.le hg hsign).trans
  exact div_le_div_of_nonneg_right
    (by simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (aligned_weight hN hb) (by norm_num : (0 : ℝ) ≤ 4000))
    (abs_nonneg _)

theorem aligned_inverse_le_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (positive : Bool) :
    (∑ rho ∈ alignedValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) ≤
        sharpCount chi (sourceL N ^ 8) / sourceL N ^ 4 := by
  have hL := sourceL_pos hN
  calc
    _ ≤ ∑ rho ∈ alignedValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℝ) / sourceL N ^ 4 := by
      apply Finset.sum_le_sum
      intro rho hr
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hL 4)
        (Finset.mem_filter.mp hr).2.1
    _ = (∑ rho ∈ alignedValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℝ)) / sourceL N ^ 4 := by
      rw [Finset.sum_div]
    _ ≤ (∑ rho ∈ zeroValues chi (sourceL N ^ 8),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) / sourceL N ^ 4 :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg (aligned_subset_height chi positive)
          (fun _ _ _ => Nat.cast_nonneg _)) (pow_nonneg hL.le 4)
    _ ≤ _ := div_le_div_of_nonneg_right
      (complete_count_le_sharp chi (pow_nonneg hL.le 8)) (pow_nonneg hL.le 4)

theorem norm_aligned_character_le_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) {positive : Bool} {eta : ℝ}
    (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖∑ rho ∈ alignedValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
        (4000 * (N : ℝ) / sourceL N ^ 12) *
          (sharpCount chi (sourceL N ^ 8) / sourceL N ^ 4) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ rho ∈ alignedValues chi N positive,
        (4000 * (N : ℝ) / sourceL N ^ 12) *
          ((analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) := by
      apply Finset.sum_le_sum
      intro rho hr
      rw [norm_mul, Complex.norm_natCast]
      convert mul_le_mul_of_nonneg_left (Jrho_aligned hN hr he) (Nat.cast_nonneg _) using 1
      ring
    _ = (4000 * (N : ℝ) / sourceL N ^ 12) *
        (∑ rho ∈ alignedValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℝ) / |rho.im|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (aligned_inverse_le_sharp hN chi positive) (by positivity)

theorem norm_alignedPacket_le_sharp {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {positive : Bool} {eta : ℝ}
    (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖alignedPacket q N a positive eta‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        ((4000 * (N : ℝ) / sourceL N ^ 12) *
          (sharpCount chi (sourceL N ^ 8) / sourceL N ^ 4)) := by
  unfold alignedPacket
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_aligned_character_le_sharp hN chi he) (norm_nonneg _)

theorem sharpCount_band_envelope {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    sharpCount chi (sourceL N ^ 8) ≤ 110 * sourceL N ^ 9 := by
  have hL := sourceL_pos hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy : (10000 : ℝ) ≤ sourceL N ^ 8 :=
    (by norm_num : (10000 : ℝ) ≤ 2000 ^ 8).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 8)
  have hl : Real.log ((q : ℝ) * sourceL N ^ 8) ≤ 11 * sourceL N := by
    calc
      _ ≤ Real.log (sourceL N ^ 11) := by
        apply Real.log_le_log (mul_pos hq0 (pow_pos hL 8))
        simpa only [sourceP, ← pow_add] using
          mul_le_mul_of_nonneg_right hq (pow_nonneg hL.le 8)
      _ = 11 * Real.log (sourceL N) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos hL]
  apply (sharpCount_le_ten chi hy).trans
  calc
    _ ≤ 10 * sourceL N ^ 8 * (11 * sourceL N) := by gcongr
    _ = _ := by ring

theorem norm_alignedPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {positive : Bool} {eta : ℝ} (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖alignedPacket q N a positive eta‖ ≤ 440000 * (N : ℝ) / sourceL N ^ 4 := by
  have hL := sourceL_pos hN
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N ^ 3 := by
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
    exact (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q :
      (q.totient : ℝ) ≤ (q : ℝ))).trans (hsq.trans hq)
  have hc (chi : Character q) :
      ‖∑ rho ∈ alignedValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
          (4000 * (N : ℝ) / sourceL N ^ 12) *
            ((110 * sourceL N ^ 9) / sourceL N ^ 4) := by
    apply (norm_aligned_character_le_sharp hN chi he).trans
    gcongr
    exact sharpCount_band_envelope hN hq chi
  apply (norm_gauss_packet_le a _ (by positivity) hc).trans
  calc
    _ ≤ sourceL N ^ 3 * ((4000 * (N : ℝ) / sourceL N ^ 12) *
        ((110 * sourceL N ^ 9) / sourceL N ^ 4)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp; ring

theorem norm_alignedPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {positive : Bool} {eta : ℝ} (he : if positive then 0 ≤ eta else eta ≤ 0) :
    ‖alignedPacket q N a positive eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hp : (4400000000 : ℝ) ≤ sourceL N ^ 3 :=
    (by norm_num : (4400000000 : ℝ) ≤ 3100 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 3)
  apply (norm_alignedPacket_le_polynomial hN0 hq he).trans
  rw [show sourceL N ^ 4 = sourceL N ^ 3 * sourceL N by ring, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ (pow_pos hL 3)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier
