import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining.Integral

/-! 全模数低高度左族的零点自由费用进一步实际付为显式多项式费用；近一费用仍按层保留。 -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining

open Interfaces Parameters ArcGeometry CompleteExpansion CharacterExpansion

theorem sharpCount_mono {q : ℕ} [NeZero q] (chi : Character q) {y z : ℝ}
    (hy : 0 ≤ y) (hyz : y ≤ z) :
    (∑ rho ∈ CompleteExpansion.zeroValues chi y, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
      sharpCount chi z := by
  apply le_trans _ (complete_count_le_sharp chi (hy.trans hyz))
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
  intro rho hr
  obtain ⟨hz, h0, h1, ht, hb⟩ := mem_zeroValues.mp hr
  exact mem_zeroValues.mpr ⟨hz, h0, h1, ht.trans hyz, hb⟩

theorem full_low_count_product {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    (q : ℝ) * sharpCount chi (max 10000 (lowHeight N q)) ≤
      450000 * sourceL N ^ 3 * Real.log (sourceL N) := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  let y := max 10000 (lowHeight N q)
  have hy : (10000 : ℝ) ≤ y := le_max_left _ _
  have hprod : (q : ℝ) * y ≤ 10000 * sourceL N ^ 3 := by
    rcases le_total (lowHeight N q) 10000 with hh | hh
    · simp only [y, max_eq_left hh]
      simpa only [sourceP, mul_comm] using mul_le_mul_of_nonneg_right hq (by norm_num : (0 : ℝ) ≤ 10000)
    · simp only [y, max_eq_right hh]
      have he : (q : ℝ) * lowHeight N q = (3.36 / 10000 : ℝ) * sourceL N ^ 3 := by
        unfold lowHeight omegaCutoff sourceP
        field_simp
      rw [he]
      nlinarith [pow_nonneg hL.le 3]
  have hlog10000 : Real.log 10000 ≤ (3 / 2 : ℝ) * Real.log (sourceL N) := by
    have hp : (10000 : ℝ) ^ 2 ≤ sourceL N ^ 3 :=
      (by norm_num : (10000 : ℝ) ^ 2 ≤ 3100 ^ 3).trans
        (pow_le_pow_left₀ (by norm_num) (sourceL_ge_3100 hN) 3)
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 10000 ^ 2) hp
    simp only [Real.log_pow, Nat.cast_ofNat] at hh
    linarith
  have hlog : Real.log ((q : ℝ) * y) ≤ (9 / 2 : ℝ) * Real.log (sourceL N) := by
    have hh := Real.log_le_log (mul_pos hq0 (by linarith : 0 < y)) hprod
    rw [Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) (pow_pos hL 3).ne',
      Real.log_pow] at hh
    simp only [Nat.cast_ofNat] at hh
    linarith
  calc
    _ ≤ (q : ℝ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      mul_le_mul_of_nonneg_left (sharpCount_le_ten chi hy) hq0.le
    _ = 10 * ((q : ℝ) * y) * Real.log ((q : ℝ) * y) := by ring
    _ ≤ 10 * (10000 * sourceL N ^ 3) * ((9 / 2 : ℝ) * Real.log (sourceL N)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num)) hlog
        (Real.log_nonneg (by nlinarith)) (by positivity)
    _ = _ := by ring

def leftScalarFee (N : ℕ) : ℝ :=
  4050000 * (N : ℝ) * Real.log (sourceL N) / (sourceL N ^ 3 * Real.sqrt (sourceL N))

theorem norm_leftPacket_scalar {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (positive : Bool)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => leftValues chi N positive) N eta‖ ≤ leftScalarFee N := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hP := sourceP_pos hN0
  have hl : 0 ≤ Real.log (sourceL N) := Real.log_nonneg (one_le_sourceL hN0)
  have hy : 0 ≤ lowHeight N q := div_nonneg (omegaCutoff_pos hN0 (NeZero.pos q)).le (by norm_num)
  have hs : Real.sqrt (q.totient : ℝ) ≤ sourceL N * Real.sqrt (sourceL N) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hh : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
      have heq : (sourceL N * Real.sqrt (sourceL N)) ^ 2 = sourceL N ^ 3 := by
        rw [mul_pow, Real.sq_sqrt hL.le]
        ring
      rw [heq]
      exact hh.trans hq
  have hc (chi : Character q) :
      ‖∑ rho ∈ leftValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta‖ ≤
      4050000 * (N : ℝ) * Real.log (sourceL N) / sourceL N ^ 5 := by
    have hcount : (q : ℝ) * (∑ rho ∈ leftValues chi N positive,
        (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
        450000 * sourceL N ^ 3 * Real.log (sourceL N) := by
      have hh : (∑ rho ∈ leftValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤
          sharpCount chi (max 10000 (lowHeight N q)) := by
        apply le_trans _ (sharpCount_mono chi hy (le_max_right _ _))
        exact Finset.sum_le_sum_of_subset_of_nonneg
          ((Finset.filter_subset _ _).trans (largeLow_subset_zero chi positive))
          (fun _ _ _ => Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg q)).trans
        (full_low_count_product hN hq chi)
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ rho ∈ leftValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ) *
          ((1 / sourceL N ^ 5) * lowKernel N q) := by
        apply Finset.sum_le_sum
        intro rho hr
        rw [norm_mul, Complex.norm_natCast]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact (Jrho_left hN hr he).trans (mul_le_mul_of_nonneg_right
          (outerWeight_le_log_fifth hN) (by unfold lowKernel; positivity))
      _ = ((q : ℝ) * ∑ rho ∈ leftValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
          (9 * (N : ℝ) / sourceL N ^ 8) := by
        rw [← Finset.sum_mul]
        unfold lowKernel sourceP
        field_simp
      _ ≤ (450000 * sourceL N ^ 3 * Real.log (sourceL N)) *
          (9 * (N : ℝ) / sourceL N ^ 8) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by field_simp; ring
  apply (norm_gauss_packet_le a _ (by positivity) hc).trans
  calc
    _ ≤ (sourceL N * Real.sqrt (sourceL N)) *
        (4050000 * (N : ℝ) * Real.log (sourceL N) / sourceL N ^ 5) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by
      unfold leftScalarFee
      have hs0 := Real.sqrt_pos.mpr hL
      field_simp
      rw [Real.sq_sqrt hL.le]

theorem leftScalarFee_le_069 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    leftScalarFee N ≤ 0.069 * (N : ℝ) / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hs : (55 : ℝ) ≤ Real.sqrt (sourceL N) :=
    (Real.le_sqrt (by norm_num) hL.le).mpr (by linarith [sourceL_ge_3100 hN])
  have hlog := log_ratio_endpoint hN
  have h1 : (1 : ℝ) / sourceL N ≤ 1 / 3100 :=
    one_div_le_one_div_of_le (by norm_num) (sourceL_ge_3100 hN)
  have h2 : (1 : ℝ) / Real.sqrt (sourceL N) ≤ 1 / 55 :=
    one_div_le_one_div_of_le (by norm_num) hs
  have heq : leftScalarFee N =
      (4050000 * (Real.log (sourceL N) / sourceL N) *
        (1 / sourceL N) * (1 / Real.sqrt (sourceL N))) * ((N : ℝ) / sourceL N) := by
    unfold leftScalarFee
    ring
  rw [heq]
  have hb : 4050000 * (Real.log (sourceL N) / sourceL N) *
      (1 / sourceL N) * (1 / Real.sqrt (sourceL N)) ≤ (0.069 : ℝ) := by
    calc
      4050000 * (Real.log (sourceL N) / sourceL N) *
          (1 / sourceL N) * (1 / Real.sqrt (sourceL N)) ≤
          (4050000 : ℝ) * (9 / 3100) * (1 / 3100) * (1 / 55) := by
        apply mul_le_mul _ h2 (by positivity) (by norm_num)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num)) h1
          (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_right hb (div_nonneg (Nat.cast_nonneg N) hL.le)

def alternativePacketFee (N q : ℕ) : ℝ :=
  lowKernel N q * (gaussCap q / (q.totient : ℝ) * (7 + 14000 * innerWeight N)) + leftScalarFee N

theorem norm_largeLowPacket_alternative {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hi : sourceIndex a q) (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => largeLowValues chi N positive) N eta‖ ≤ alternativePacketFee N q := by
  rw [largeLowPacket_eq_three]
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans (add_le_add
    (norm_closePacket hN hq hi positive he) (norm_middlePacket hN hq hi positive he)))
    (norm_leftPacket_scalar hN hq positive he)).trans_eq
  unfold alternativePacketFee
  ring

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Remaining
