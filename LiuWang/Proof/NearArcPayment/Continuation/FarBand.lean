import LiuWang.Proof.NearArcPayment.Continuation.RealBand

/-!
# A fully paid low-height oscillatory band

The band includes real and nonreal zeros. Its height is omega/10000, so the
same M1-complement inequality forces the strong far kernel for nonreal zeros.
This single band includes the real payment; it is not charged twice.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion OscillatoryBounds

def farPaidValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (rightValues chi N).filter (fun rho =>
    |rho.im| ≤ omegaCutoff N q / 10000 ∧ rho.re ≤ realCutoff N)

def unpaidValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (rightValues chi N).filter (fun rho =>
    ¬ (|rho.im| ≤ omegaCutoff N q / 10000 ∧ rho.re ≤ realCutoff N))

def farPaidPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ farPaidValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

def unpaidPacket (q : ℕ) [NeZero q] (N a : ℕ) (eta : ℝ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
    ∑ rho ∈ unpaidValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta

theorem rightPacket_eq_far_add_unpaid {q : ℕ} [NeZero q] (N a : ℕ) (eta : ℝ) :
    rightPacket q N a eta = farPaidPacket q N a eta + unpaidPacket q N a eta := by
  unfold rightPacket farPaidPacket unpaidPacket farPaidValues unpaidValues
  simp only [← mul_add, ← Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  congr 1
  apply Finset.sum_congr rfl
  intro rho _
  by_cases h : |rho.im| ≤ omegaCutoff N q / 10000 ∧ rho.re ≤ realCutoff N <;> simp [h]

theorem realPaidValues_subset_far {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) :
    realPaidValues chi N ⊆ farPaidValues chi N := by
  intro rho hr
  obtain ⟨hr, hg, hb⟩ := Finset.mem_filter.mp hr
  refine Finset.mem_filter.mpr ⟨hr, ?_, hb⟩
  simp only [hg, abs_zero]
  exact div_nonneg (omegaCutoff_pos hN (NeZero.pos q)).le (by norm_num)

theorem farPaid_height_le_P {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) :
    max 10000 (omegaCutoff N q / 10000) ≤ sourceP N := by
  have hP := sourceP_pos hN
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by linarith
  apply max_le
  · exact (by norm_num : (10000 : ℝ) ≤ 2000 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_2000 hN) 3)
  · unfold omegaCutoff
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < (q : ℝ) * 10000)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq1 hP.le]

theorem farPaid_count_le {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    (∑ rho ∈ farPaidValues chi N, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      60 * sourceL N ^ 4 := by
  let y := max 10000 (omegaCutoff N q / 10000)
  have hy : (10000 : ℝ) ≤ y := le_max_left _ _
  have hyP : y ≤ sourceP N := farPaid_height_le_P hN
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hL := sourceL_pos hN
  have hP := sourceP_pos hN
  have hs : farPaidValues chi N ⊆ zeroValues chi y := by
    intro rho hr
    obtain ⟨hr, ht, _⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr, _⟩ := Finset.mem_filter.mp hr
    obtain ⟨hz, h0, h1, _, hh⟩ := mem_zeroValues.mp hr
    exact mem_zeroValues.mpr ⟨hz, h0, h1, ht.trans (le_max_right _ _), hh⟩
  have hlog : Real.log ((q : ℝ) * y) ≤ 6 * sourceL N := by
    calc
      _ ≤ Real.log (sourceL N ^ 6) := by
        apply Real.log_le_log (mul_pos hq0 (by linarith))
        have hh := mul_le_mul hq hyP (by linarith) (sourceP_pos hN).le
        simpa only [sourceP, ← pow_add] using hh
      _ = 6 * Real.log (sourceL N) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos hL]
  calc
    _ ≤ ∑ rho ∈ zeroValues chi y, (analyticOrderNatAt chi.LFunction rho : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ 10 * y * Real.log ((q : ℝ) * y) := count_complete_le chi hy
    _ ≤ 10 * sourceP N * (6 * sourceL N) := by
      have hl : 0 ≤ Real.log ((q : ℝ) * y) := Real.log_nonneg (by nlinarith)
      gcongr
    _ = _ := by unfold sourceP; ring

theorem Jrho_farPaid {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {eta : ℝ} (he : deltaRadius N q < |eta|)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ farPaidValues chi N) :
    ‖Jrho N rho eta‖ ≤ 9 * (N : ℝ) / sourceL N ^ 10 := by
  have hL := sourceL_pos hN
  obtain ⟨hr, ht, hb⟩ := Finset.mem_filter.mp hr
  obtain ⟨hr, _⟩ := Finset.mem_filter.mp hr
  have hb1 := (mem_zeroValues.mp hr).2.2.1.le
  by_cases hg : rho.im = 0
  · exact (Jrho_real_paid hN (NeZero.pos q) hq he hb1 hg hb).trans (by gcongr; norm_num)
  · have hf := tiny_height_is_far hN (NeZero.pos q) he ht
    calc
      _ ≤ (3 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |eta| :=
        Jrho_far_three_pi (nat_pos_of_exp_le hN) hb1 hg hf
      _ = 3 * ((0.001 * (N : ℝ)) ^ (rho.re - 1) * (1 / (Real.pi * |eta|))) := by ring
      _ ≤ 3 * ((1 / sourceL N ^ 10) * (3 * (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul (real_weight_le_log_power hN hb)
          (reciprocal_on_M2 hN (NeZero.pos q) hq he) (by positivity) (by positivity)
      _ = _ := by ring

theorem norm_gauss_packet_le {q : ℕ} [NeZero q] (a : ℕ)
    (F : Character q → ℂ) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ chi, ‖F chi‖ ≤ B) :
    ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi * F chi‖ ≤
      Real.sqrt (q.totient : ℝ) * B := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF chi) (norm_nonneg _)
    _ = ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖) * B := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ ((q.totient : ℝ)⁻¹ *
        (Real.sqrt (q.totient : ℝ) * (q.totient : ℝ))) * B := by
      gcongr
      exact NonprincipalPacket.sum_norm_G_le a
    _ = _ := by field_simp

theorem norm_farPaidPacket_le_polynomial {N a q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖farPaidPacket q N a eta‖ ≤ 540 * (N : ℝ) / sourceL N ^ 3 := by
  have hL := sourceL_pos hN
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N ^ 3 := by
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
    exact (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le q :
      (q.totient : ℝ) ≤ (q : ℝ))).trans (hsq.trans hq)
  have hchar (chi : Character q) :
      ‖∑ rho ∈ farPaidValues chi N,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      (60 * sourceL N ^ 4) * (9 * (N : ℝ) / sourceL N ^ 10) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ rho ∈ farPaidValues chi N, (analyticOrderNatAt chi.LFunction rho : ℝ) *
          (9 * (N : ℝ) / sourceL N ^ 10) := by
        apply Finset.sum_le_sum
        intro rho hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (Jrho_farPaid hN hq he hr) (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (farPaid_count_le hN hq chi) (by positivity)
  apply (norm_gauss_packet_le a _ (by positivity) hchar).trans
  calc
    _ ≤ sourceL N ^ 3 * ((60 * sourceL N ^ 4) * (9 * (N : ℝ) / sourceL N ^ 10)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp; ring

theorem norm_farPaidPacket_le_paid {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖farPaidPacket q N a eta‖ ≤ 0.0001 * (N : ℝ) / sourceL N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hp : (5400000 : ℝ) ≤ sourceL N ^ 2 :=
    (by norm_num : (5400000 : ℝ) ≤ 3100 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 2)
  apply (norm_farPaidPacket_le_polynomial hN0 hq he).trans
  rw [show sourceL N ^ 3 = sourceL N ^ 2 * sourceL N by ring, div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (div_le_iff₀ (pow_pos hL 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) N)]

end LiuWang.Proof.NearArcPayment.Continuation
