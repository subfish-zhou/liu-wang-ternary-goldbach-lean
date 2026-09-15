import LiuWang.Proof.NearArcPayment.Continuation.Frontier.SignIntegral

/-! 对前次同号付款后留下的中高度带，真实平方根高度核继续付款。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier

open Interfaces Parameters CompleteExpansion CharacterExpansion

def squareCutoff (N : ℕ) : ℝ := 1 - 14 * Real.log (sourceL N) / sourceL N

def squareValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (remainingValues chi N positive).filter (fun rho =>
    sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧ rho.re ≤ squareCutoff N)

def tailValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ)
    (positive : Bool) : Finset ℂ :=
  (remainingValues chi N positive).filter (fun rho =>
    ¬ (sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧ rho.re ≤ squareCutoff N))

def squarePacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ squareValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def tailPacket (q : ℕ) [NeZero q] (N a : ℕ) (positive : Bool) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ tailValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem remainingPacket_eq_square_add_tail {q : ℕ} [NeZero q]
    (N a : ℕ) (positive : Bool) (eta : ℝ) :
    remainingPacket q N a positive eta =
      squarePacket q N a positive eta + tailPacket q N a positive eta := by
  unfold remainingPacket squarePacket tailPacket squareValues tailValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hh : sourceL N ^ 4 ≤ |rho.im| ∧ |rho.im| ≤ sourceL N ^ 8 ∧
      rho.re ≤ squareCutoff N <;> simp [hh]

theorem square_weight {N : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) {beta : ℝ}
    (hb : beta ≤ squareCutoff N) :
    (N : ℝ) ^ beta ≤ (N : ℝ) / sourceL N ^ 14 := by
  have hn := natCast_pos_of_exp_le hN
  have hL := sourceL_pos hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have heq : (N : ℝ) ^ (squareCutoff N) = (N : ℝ) / sourceL N ^ 14 := by
    unfold squareCutoff
    rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_def_of_pos hn]
    change (N : ℝ) / Real.exp (sourceL N * (14 * Real.log (sourceL N) / sourceL N)) = _
    rw [show sourceL N * (14 * Real.log (sourceL N) / sourceL N) =
      14 * Real.log (sourceL N) by field_simp]
    rw [show (14 : ℝ) * Real.log (sourceL N) = Real.log (sourceL N ^ 14) by
      rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL 14)]
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hb).trans_eq heq

theorem square_subset_height {N q : ℕ} [NeZero q]
    (chi : Character q) (positive : Bool) :
    squareValues chi N positive ⊆ zeroValues chi (sourceL N ^ 8) := by
  intro rho hr
  obtain ⟨hr, _, hu, _⟩ := Finset.mem_filter.mp hr
  have hf := (Finset.mem_filter.mp hr).1
  obtain ⟨hz, h0, h1, _, hb, _⟩ := (finalValues_literal chi).mp hf
  exact mem_zeroValues.mpr ⟨hz, h0, h1, hu, by linarith⟩

theorem Jrho_square {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) {chi : Character q} {rho : ℂ}
    {positive : Bool} (hr : rho ∈ squareValues chi N positive) (eta : ℝ) :
    ‖Jrho N rho eta‖ ≤
      (10000 * (N : ℝ) / sourceL N ^ 14) / Real.sqrt |rho.im| := by
  obtain ⟨hr, hl, _, hb⟩ := Finset.mem_filter.mp hr
  obtain ⟨_, h0, h1, _⟩ := (finalValues_literal chi).mp (Finset.mem_filter.mp hr).1
  have hg : rho.im ≠ 0 := abs_pos.mp ((pow_pos (sourceL_pos hN) 4).trans_le hl)
  have hc : (0.001 : ℝ) ^ (rho.re - 1) ≤ 1000 := by
    have hh := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 0.001)
      (by norm_num : (0.001 : ℝ) ≤ 1) (show (-1 : ℝ) ≤ rho.re - 1 by linarith)
    norm_num at hh
    simpa only [show (0.001 : ℝ) = 1 / 1000 by norm_num] using hh
  apply (OscillatoryBounds.Jrho_sqrt_ten (nat_pos_of_exp_le hN) h1.le hg eta).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    _ ≤ 10 * 1000 * ((N : ℝ) / sourceL N ^ 14) := by
      apply mul_le_mul _ (square_weight hN hb) (by positivity) (by norm_num)
      exact mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring

theorem square_inverse_sqrt_le_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (positive : Bool) :
    (∑ rho ∈ squareValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) ≤
        sharpCount chi (sourceL N ^ 8) / sourceL N ^ 2 := by
  have hL := sourceL_pos hN
  have hl {rho : ℂ} (hr : rho ∈ squareValues chi N positive) :
      sourceL N ^ 2 ≤ Real.sqrt |rho.im| := by
    apply (Real.le_sqrt (sq_nonneg _) (abs_nonneg _)).mpr
    simpa only [← pow_mul] using (Finset.mem_filter.mp hr).2.1
  calc
    _ ≤ ∑ rho ∈ squareValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℝ) / sourceL N ^ 2 := by
      apply Finset.sum_le_sum
      intro rho hr
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hL 2) (hl hr)
    _ = (∑ rho ∈ squareValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℝ)) / sourceL N ^ 2 := by rw [Finset.sum_div]
    _ ≤ (∑ rho ∈ zeroValues chi (sourceL N ^ 8),
        (analyticOrderNatAt chi.LFunction rho : ℝ)) / sourceL N ^ 2 :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg (square_subset_height chi positive)
          (fun _ _ _ => Nat.cast_nonneg _)) (pow_nonneg hL.le 2)
    _ ≤ _ := div_le_div_of_nonneg_right
      (complete_count_le_sharp chi (pow_nonneg hL.le 8)) (pow_nonneg hL.le 2)

theorem norm_square_character_le_sharp {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (positive : Bool) (eta : ℝ) :
    ‖∑ rho ∈ squareValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
        (10000 * (N : ℝ) / sourceL N ^ 14) *
          (sharpCount chi (sourceL N ^ 8) / sourceL N ^ 2) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ rho ∈ squareValues chi N positive,
        (10000 * (N : ℝ) / sourceL N ^ 14) *
          ((analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) := by
      apply Finset.sum_le_sum
      intro rho hr
      rw [norm_mul, Complex.norm_natCast]
      convert mul_le_mul_of_nonneg_left (Jrho_square hN hr eta) (Nat.cast_nonneg _) using 1
      ring
    _ = (10000 * (N : ℝ) / sourceL N ^ 14) *
        (∑ rho ∈ squareValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℝ) / Real.sqrt |rho.im|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (square_inverse_sqrt_le_sharp hN chi positive) (by positivity)

theorem norm_squarePacket_le_sharp {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (positive : Bool) (eta : ℝ) :
    ‖squarePacket q N a positive eta‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ *
        ((10000 * (N : ℝ) / sourceL N ^ 14) *
          (sharpCount chi (sourceL N ^ 8) / sourceL N ^ 2)) := by
  unfold squarePacket
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_square_character_le_sharp hN chi positive eta)
    (norm_nonneg _)

theorem norm_squarePacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (positive : Bool) (eta : ℝ) :
    ‖squarePacket q N a positive eta‖ ≤ 1100000 * (N : ℝ) / sourceL N ^ 4 := by
  have hL := sourceL_pos hN
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N ^ 3 := by
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
    exact (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q :
      (q.totient : ℝ) ≤ (q : ℝ))).trans (hsq.trans hq)
  have hc (chi : Character q) :
      ‖∑ rho ∈ squareValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
          (10000 * (N : ℝ) / sourceL N ^ 14) *
            ((110 * sourceL N ^ 9) / sourceL N ^ 2) := by
    apply (norm_square_character_le_sharp hN chi positive eta).trans
    gcongr
    exact sharpCount_band_envelope hN hq chi
  apply (norm_gauss_packet_le a _ (by positivity) hc).trans
  calc
    _ ≤ sourceL N ^ 3 * ((10000 * (N : ℝ) / sourceL N ^ 14) *
        ((110 * sourceL N ^ 9) / sourceL N ^ 2)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp; ring

theorem norm_squarePacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (positive : Bool) (eta : ℝ) :
    ‖squarePacket q N a positive eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hp : (11000000000 : ℝ) ≤ sourceL N ^ 3 :=
    (by norm_num : (11000000000 : ℝ) ≤ 3100 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 3)
  apply (norm_squarePacket_le_polynomial hN0 hq positive eta).trans
  rw [show sourceL N ^ 4 = sourceL N ^ 3 * sourceL N by ring, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ (pow_pos hL 3)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation.Frontier
