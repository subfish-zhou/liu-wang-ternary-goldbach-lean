import LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual.Integral

/-! 同一 q 的严格 M1 补集把整个低高度非实余族放入真正的远相位区。 -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual

open Interfaces Parameters CompleteExpansion CharacterExpansion NearOneDensity ArcGeometry

theorem log_square_strong {x : ℝ} (hx : 3100 ≤ x) :
    (Real.log x) ^ 2 ≤ (1089 / 16 : ℝ) * x / 3100 := by
  have hx0 : 0 < x := by linarith
  have hbase : Real.log 3100 ≤ 33 / 4 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hh := Real.quadratic_le_exp_of_nonneg (x := 33 / 128) (by norm_num)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 33 / 128 + (33 / 128) ^ 2 / 2) hh 32
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have hs1 : 1 ≤ Real.sqrt (x / 3100) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    linarith
  have he : Real.log x = Real.log 3100 + 2 * Real.log (Real.sqrt (x / 3100)) := by
    rw [Real.log_sqrt (by positivity), Real.log_div hx0.ne' (by norm_num)]
    ring
  have hl : Real.log x ≤ (33 / 4) * Real.sqrt (x / 3100) := by
    rw [he]
    linarith [Real.log_le_sub_one_of_pos
      (Real.sqrt_pos.mpr (by positivity : 0 < x / 3100))]
  have hn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ x / 3100)]

theorem left_low_weight {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {beta : ℝ} (hb : beta ≤ realAlpha N) :
    (0.001 * (N : ℝ)) ^ (beta - 1) ≤ 1 / sourceL N ^ 3 := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hL := sourceL_pos hN0
  have hl : 0 < Real.log (sourceL N) := Real.log_pos (by linarith [sourceL_ge_3100 hN])
  have hw := sourceWindow_gt_one hN0
  have hlw : 0 < Real.log (0.001 * (N : ℝ)) := Real.log_pos hw
  have hs := log_square_strong (sourceL_ge_3100 hN)
  have hprod : 12 * Real.log (sourceL N) ^ 2 ≤
      0.27 * Real.log (0.001 * (N : ℝ)) := by
    nlinarith [window_log_lower hN, sourceL_ge_3100 hN]
  have ha : beta - 1 ≤ -(0.27 / (4 * Real.log (sourceL N))) := by
    simp only [realAlpha, realScale, Real.log_pow, Nat.cast_ofNat] at hb
    linarith
  have hd : 3 * Real.log (sourceL N) ≤
      0.27 * Real.log (0.001 * (N : ℝ)) / (4 * Real.log (sourceL N)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hprod]
  have hh := mul_le_mul_of_nonneg_left ha hlw.le
  have he : Real.log (0.001 * (N : ℝ)) * -(0.27 / (4 * Real.log (sourceL N))) =
      -(0.27 * Real.log (0.001 * (N : ℝ)) / (4 * Real.log (sourceL N))) := by ring
  rw [he] at hh
  rw [Real.rpow_def_of_pos (by linarith : 0 < 0.001 * (N : ℝ))]
  calc
    _ ≤ Real.exp (-(3 * Real.log (sourceL N))) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_neg, show 3 * Real.log (sourceL N) = Real.log (sourceL N ^ 3) by
        rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hL 3)]
      simp only [one_div]

def lowHeight (N q : ℕ) : ℝ := omegaCutoff N q / 10000

def lowValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (afterRealValues chi N positive).filter
    (fun rho => (q : ℝ) ≤ realModulusLimit N ∧ |rho.im| ≤ lowHeight N q)

def restValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (afterRealValues chi N positive).filter
    (fun rho => ¬ ((q : ℝ) ≤ realModulusLimit N ∧ |rho.im| ≤ lowHeight N q))

def upperLowValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (lowValues chi N positive).filter (fun rho => realAlpha N ≤ rho.re)

def lowerLowValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) (positive : Bool) : Finset ℂ :=
  (lowValues chi N positive).filter (fun rho => rho.re < realAlpha N)

theorem low_nonreal {N q : ℕ} [NeZero q] {chi : Character q} {positive : Bool} {rho : ℂ}
    (hr : rho ∈ lowValues chi N positive) : rho.im ≠ 0 := by
  obtain ⟨hr, hq, _⟩ := Finset.mem_filter.mp hr
  exact fun hg => (Finset.mem_filter.mp hr).2 ⟨hq, hg⟩

theorem low_subset_zero {N q : ℕ} [NeZero q] (chi : Character q) (positive : Bool) :
    lowValues chi N positive ⊆ CompleteExpansion.zeroValues chi (lowHeight N q) := by
  intro rho hr
  obtain ⟨hr, _, ht⟩ := Finset.mem_filter.mp hr
  have hl := (Finset.mem_filter.mp hr).1
  have hh := ((lastValues_exact chi positive).mp hl).1
  have hf := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  obtain ⟨hz, h0, h1, _, hb, _⟩ := (finalValues_literal chi).mp hf
  exact mem_zeroValues.mpr ⟨hz, h0, h1, ht, by linarith⟩

theorem low_height_product {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ realModulusLimit N) :
    (q : ℝ) * max 10000 (lowHeight N q) ≤ sourceL N ^ 3 / 100 := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have ht : (q : ℝ) * lowHeight N q = (3.36 / 10000 : ℝ) * sourceL N ^ 3 := by
    unfold lowHeight omegaCutoff sourceP
    field_simp
  have hqL : (q : ℝ) * 10000 ≤ sourceL N ^ 3 / 100 := by
    unfold realModulusLimit at hq
    have hh := mul_le_mul_of_nonneg_left (sourceL_ge_3100 hN) (sq_nonneg (sourceL N))
    nlinarith
  rcases le_total (lowHeight N q) 10000 with hh | hh
  · rwa [max_eq_left hh]
  · rw [max_eq_right hh, ht]
    nlinarith [pow_pos hL 3]

theorem low_density_domain {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (hq : (q : ℝ) ≤ realModulusLimit N) :
    100000000000 ≤ realScale N ∧ (q : ℝ) * max 1 (lowHeight N q) ≤ realScale N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  refine ⟨(real_modulus_domain hN hq).1, ?_⟩
  have hh := low_height_product hN hq
  have hm : (q : ℝ) * max 1 (lowHeight N q) ≤ (q : ℝ) * max 10000 (lowHeight N q) :=
    mul_le_mul_of_nonneg_left (max_le_max (by norm_num) le_rfl) (Nat.cast_nonneg q)
  have hl : sourceL N ^ 3 / 100 ≤ realScale N := by
    unfold realScale
    have ht := mul_le_mul_of_nonneg_right (one_le_sourceL (exp_2000_le_of_exp_3100_le hN))
      (pow_nonneg hL.le 3)
    nlinarith [pow_nonneg hL.le 3]
  exact hm.trans (hh.trans hl)

theorem upperLow_count {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) :
    (∑ chi : Character q, ∑ rho ∈ upperLowValues chi N positive,
      (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
  by_cases hq : (q : ℝ) ≤ realModulusLimit N
  · obtain ⟨hz, hqy⟩ := low_density_domain hN hq
    have hh := NearOneDensity.Continuation.complete_tail_count_row .r027 hz hqy
      (alpha := realAlpha N) (by rfl)
    have hc : (∑ chi : Character q,
        ∑ rho ∈ (CompleteExpansion.zeroValues chi (lowHeight N q)).filter (fun rho => realAlpha N ≤ rho.re),
          (analyticOrderNatAt chi.LFunction rho : ℝ)) ≤ 7 := by
      norm_num [rowBound, rowMultiplicity, rowSelectedBound] at hh
      exact_mod_cast hh
    apply le_trans _ hc
    apply Finset.sum_le_sum
    intro chi _
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
    intro rho hr
    obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨low_subset_zero chi positive hr, hb⟩
  · simp [upperLowValues, lowValues, hq]

theorem Jrho_low_weight {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ lowValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤
      (0.001 * (N : ℝ)) ^ (rho.re - 1) * (9 * (q : ℝ) * (N : ℝ) / sourceL N ^ 3) := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have ht := (Finset.mem_filter.mp hr).2.2
  have hb := (mem_zeroValues.mp (low_subset_zero chi positive hr)).2.2.1.le
  have hh := OscillatoryBounds.Jrho_far_three_pi (nat_pos_of_exp_le hN) hb
    (low_nonreal hr) (tiny_height_is_far hN0 (NeZero.pos q) he ht)
  calc
    _ ≤ (3 / Real.pi) * (0.001 * (N : ℝ)) ^ (rho.re - 1) / |eta| := hh
    _ = (3 * (0.001 * (N : ℝ)) ^ (rho.re - 1)) * (1 / (Real.pi * |eta|)) := by ring
    _ ≤ (3 * (0.001 * (N : ℝ)) ^ (rho.re - 1)) *
        (3 * (q : ℝ) * (N : ℝ) / sourceP N) :=
      mul_le_mul_of_nonneg_left (reciprocal_same_q hN0 he) (by positivity)
    _ = _ := by unfold sourceP; ring

theorem Jrho_upperLow {N q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    {chi : Character q} {positive : Bool} {rho : ℂ} (hr : rho ∈ upperLowValues chi N positive)
    {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖Jrho N rho eta‖ ≤ 9 * (N : ℝ) / (400 * sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hr := (Finset.mem_filter.mp hr).1
  have hq := (Finset.mem_filter.mp hr).2.1
  have hb := (mem_zeroValues.mp (low_subset_zero chi positive hr)).2.2.1.le
  have hw : (0.001 * (N : ℝ)) ^ (rho.re - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (sourceWindow_gt_one (exp_2000_le_of_exp_3100_le hN)).le (sub_nonpos.mpr hb)
  apply (Jrho_low_weight hN hr he).trans
  calc
    _ ≤ 1 * (9 * realModulusLimit N * (N : ℝ) / sourceL N ^ 3) := by gcongr
    _ = _ := by unfold realModulusLimit; field_simp

theorem norm_upperLowPacket {N a q : ℕ} [NeZero q] (hN : Real.exp 3100 ≤ (N : ℝ))
    (positive : Bool) {eta : ℝ} (he : deltaRadius N q < |eta|) :
    ‖realPacketOn q a (fun chi => upperLowValues chi N positive) N eta‖ ≤
      63 * (N : ℝ) / (400 * sourceL N) := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  apply (norm_realPacketOn_le_weighted _ (fun _ _ hr => Jrho_upperLow hN hr he)).trans
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, (q.totient : ℝ) *
        ((∑ rho ∈ upperLowValues chi N positive, (analyticOrderNatAt chi.LFunction rho : ℝ)) *
          (9 * (N : ℝ) / (400 * sourceL N))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi _
      exact mul_le_mul_of_nonneg_right (norm_G_le_totient a chi) (by positivity)
    _ = (∑ chi : Character q, ∑ rho ∈ upperLowValues chi N positive,
          (analyticOrderNatAt chi.LFunction rho : ℝ)) * (9 * (N : ℝ) / (400 * sourceL N)) := by
      rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul, ← Finset.sum_mul]
    _ ≤ 7 * (9 * (N : ℝ) / (400 * sourceL N)) :=
      mul_le_mul_of_nonneg_right (upperLow_count hN positive) (by positivity)
    _ = _ := by ring

end LiuWang.Proof.NearArcPayment.Continuation.Frontier.Payment.Residual
