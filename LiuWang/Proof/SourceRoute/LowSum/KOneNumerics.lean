import LiuWang.Proof.SourceRoute.LowSum.TwoZeroBranch
import LiuWang.Proof.WeightedLowZeros.Continuation.SourceComparison

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.LowSum

def paperCap (N : ℕ) : ℝ := 1 - 1 / (9.645908801 * Real.log (sourceP N))

theorem coefficient_cap_small {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a : ℝ} (ha : a ≤ 0.33) : coefficient (cap N a) ≤ 1.0122 := by
  have hl : 25.3294 ≤ Real.log (lowScale N) := original_log_scale_lower (sourceL_ge_3100 hN)
  have hc : 0.9869 ≤ cap N a := by
    have hd : a / Real.log (lowScale N) ≤ 0.0131 :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    dsimp [cap]
    linarith
  have hp : 0 < cap N a := by linarith
  exact (coefficient_antitone (by norm_num : (0 : ℝ) < 0.9869) hp hc).trans
    (coefficient_le_of_rational_test (by norm_num : (0 : ℝ) < 0.9869) (by norm_num) (by norm_num))

theorem seed_012 : 4.185e-7 ≤ seedExp 0.12 ∧ seedExp 0.12 ≤ 4.187e-7 := by
  apply seed_enclosure (n := 14) (xl := 0.6864) (xu := 0.6865) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_015 : 1.064e-8 ≤ seedExp 0.15 ∧ seedExp 0.15 ≤ 1.065e-8 := by
  apply seed_enclosure (n := 18) (xl := 0.3580) (xu := 0.3581) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_02067 : 1.031e-11 ≤ seedExp 0.2067 ∧ seedExp 0.2067 ≤ 1.032e-11 := by
  apply seed_enclosure (n := 25) (xl := 0.2974) (xu := 0.2975) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_026213 : 1.167e-14 ≤ seedExp 0.26213 ∧ seedExp 0.26213 ≤ 1.168e-14 := by
  apply seed_enclosure (n := 32) (xl := 0.0813) (xu := 0.0814) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_02743 : 2.632e-15 ≤ seedExp 0.2743 ∧ seedExp 0.2743 ≤ 2.634e-15 := by
  apply seed_enclosure (n := 33) (xl := 0.5708) (xu := 0.5709) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem small_segment_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a b D C U E : ℝ} (hU : seedExp b ≤ U) (hE : E ≤ seedExp a)
    (hb : 0.1 ≤ b) (hba : b ≤ a) (ha : a ≤ 0.33) (hD : 0 ≤ D)
    (hcost : D * 1.0122 * (25.32942 / 25.3294) * 3100 * (U - E) ≤ C) :
    (∫ alpha in cap N a..cap N b, D * kernel N alpha) ≤ C / sourceL N := by
  have h := segment_integral_le_of_coefficient hN hb hba (by linarith) hD
    (by norm_num) (coefficient_cap_small hN ha)
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
  have hd : seedExp b - seedExp a ≤ U - E := by linarith
  exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans hcost

theorem original_K1_middle {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.33..cap N 0.2743, 13 * kernel N alpha) +
      (∫ alpha in cap N 0.2743..cap N 0.12, 2 * kernel N alpha) ≤ 0.0027 / sourceL N := by
  have h1 : (∫ alpha in cap N 0.33..cap N 0.2743, 13 * kernel N alpha) ≤
      1.08e-10 / sourceL N := by
    apply small_segment_paid hN seed_02743.2 seed_033.1 <;> norm_num
  have h2 : (∫ alpha in cap N 0.2743..cap N 0.12, 2 * kernel N alpha) ≤
      0.002628 / sourceL N := by
    apply small_segment_paid hN seed_012.2 seed_02743.1 <;> norm_num
  apply (add_le_add h1 h2).trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

theorem original_K1_last {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.33..cap N 0.26213, 13 * kernel N alpha) +
      (∫ alpha in cap N 0.26213..cap N 0.2067, 4 * kernel N alpha) +
      (∫ alpha in cap N 0.2067..cap N 0.15, 2 * kernel N alpha) ≤ 0.0001 / sourceL N := by
  have h1 : (∫ alpha in cap N 0.33..cap N 0.26213, 13 * kernel N alpha) ≤
      4.8e-10 / sourceL N := by
    apply small_segment_paid hN seed_026213.2 seed_033.1 <;> norm_num
  have h2 : (∫ alpha in cap N 0.26213..cap N 0.2067, 4 * kernel N alpha) ≤
      1.3e-7 / sourceL N := by
    apply small_segment_paid hN seed_02067.2 seed_026213.1 <;> norm_num
  have h3 : (∫ alpha in cap N 0.2067..cap N 0.15, 2 * kernel N alpha) ≤
      0.000067 / sourceL N := by
    apply small_segment_paid hN seed_015.2 seed_02067.1 <;> norm_num
  apply (add_le_add (add_le_add h1 h2) h3).trans
  rw [← add_div, ← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

theorem ratio_fifth_le_first {L : ℝ} (hL : 3100 ≤ L) : (3100 / L) ^ 5 ≤ 3100 / L := by
  have hp : 0 < L := by linarith
  have ht0 : 0 ≤ 3100 / L := by positivity
  have ht1 : 3100 / L ≤ 1 := (div_le_one hp).mpr hL
  have h4 : (3100 / L) ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  nlinarith [mul_le_mul_of_nonneg_right h4 ht0,
    show (3100 / L) ^ 5 = (3100 / L) ^ 4 * (3100 / L) by ring]

theorem exp_neg_1332 : Real.exp (-13.32 : ℝ) ≤ 1.65e-6 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.32) 7
  have he : (1 / (1.65e-6) : ℝ) ≤ Real.exp 13.32 := by
    calc
      _ ≤ (2.7182818283 : ℝ) ^ 13 *
          (∑ i ∈ Finset.range 7, (0.32 : ℝ) ^ i / i.factorial) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 1 ^ 13 * Real.exp 0.32 :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 13)
          hs (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / (1.65e-6)) he
  simpa only [Real.exp_neg, one_div, inv_inv] using h

theorem paper_endpoint_decay {L : ℝ} (hL : 3100 ≤ L) :
    Real.exp (-L / (9.645908801 * Real.log (L ^ 3))) ≤ 1.65e-6 * 3100 / L := by
  let z := Real.log (L / 3100)
  have hp : 0 < L := by linarith
  have hz : 0 ≤ z := Real.log_nonneg (by linarith)
  have he : Real.exp z = L / 3100 := Real.exp_log (by positivity)
  have hquad := Real.quadratic_le_exp_of_nonneg hz
  rw [he] at hquad
  have hlo : 8 ≤ Real.log L :=
    log_3100_bounds.1.trans (Real.log_le_log (by norm_num) hL)
  have hlog : 0 < Real.log (L ^ 3) := by rw [Real.log_pow]; positivity
  have hhi : Real.log (L ^ 3) ≤ 24.12 + 3 * z := by
    dsimp [z]
    rw [Real.log_pow, Real.log_div hp.ne' (by norm_num)]
    linarith [log_3100_bounds.2]
  have hprod := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 13.32 + 5 * z by positivity)
  have hgap : (13.32 + 5 * z) * (9.645908801 * Real.log (L ^ 3)) ≤ L := by
    nlinarith [sq_nonneg z]
  have hquot : 13.32 + 5 * z ≤ L / (9.645908801 * Real.log (L ^ 3)) :=
    (le_div_iff₀ (by positivity)).mpr hgap
  calc
    _ ≤ Real.exp (-13.32 - 5 * z) := Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
    _ = Real.exp (-13.32) * (3100 / L) ^ 5 := by
      have he5 : Real.exp (5 * z) = Real.exp z ^ 5 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul z 5
      rw [Real.exp_sub, he5, he]
      field_simp
    _ ≤ 1.65e-6 * (3100 / L) ^ 5 :=
      mul_le_mul_of_nonneg_right exp_neg_1332 (by positivity)
    _ ≤ 1.65e-6 * (3100 / L) :=
      mul_le_mul_of_nonneg_left (ratio_fifth_le_first hL) (by norm_num)
    _ = _ := by ring

theorem integral_constant_le_of_coefficient {N : ℕ} (hN : 0 < N)
    {a b D A : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D)
    (hcoef : coefficient a ≤ A) :
    (∫ alpha in a..b, D * kernel N alpha) ≤
      D * A * ((N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1)) := by
  have hdiff : 0 ≤ (N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1) :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith))
  rw [intervalIntegral.integral_const_mul]
  calc
    _ ≤ D * (coefficient a * ((N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1))) :=
      mul_le_mul_of_nonneg_left (integral_kernel_le_endpoint_difference hN ha hab) hD
    _ = D * coefficient a * ((N : ℝ) ^ (b - 1) - (N : ℝ) ^ (a - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hD) hdiff

theorem original_K1_small_expression {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.33..cap N 0.3221, 13 * kernel N alpha) +
      (∫ alpha in cap N 0.3221..paperCap N, 2 * kernel N alpha) ≤
        1.0122 * (2 * (N : ℝ) ^ (paperCap N - 1) +
          11 * (N : ℝ) ^ (cap N 0.3221 - 1) - 13 * (N : ℝ) ^ (cap N 0.33 - 1)) := by
  have hcap : cap N 0.3221 ≤ paperCap N := by
    have h1 : cap N 0.3221 ≤ cap N 0.11 := cap_order hN (by norm_num)
    have h2 : cap N 0.11 ≤ paperCap N := by
      dsimp [cap, paperCap]
      linarith [paper_gap_le_low_gap hN]
    exact h1.trans h2
  have h1 := integral_constant_le_of_coefficient (nat_pos_of_exp_le hN)
    (a := cap N 0.33) (b := cap N 0.3221) (D := 13) (A := 1.0122)
    (by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)])
    (cap_order hN (by norm_num)) (by norm_num) (coefficient_cap_small hN (by norm_num))
  have h2 := integral_constant_le_of_coefficient (nat_pos_of_exp_le hN)
    (a := cap N 0.3221) (b := paperCap N) (D := 2) (A := 1.0122)
    (by linarith [cap_ge_098 hN (by norm_num : (0.3221 : ℝ) ≤ 0.478)])
    hcap (by norm_num) (coefficient_cap_small hN (by norm_num))
  linarith

theorem original_K1_small {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.33..cap N 0.3221, 13 * kernel N alpha) +
      (∫ alpha in cap N 0.3221..paperCap N, 2 * kernel N alpha) ≤ 0.0104 / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hp : 0 < sourceL N := by linarith
  have heP : (N : ℝ) ^ (paperCap N - 1) ≤ 1.65e-6 * 3100 / sourceL N := by
    have hid : (N : ℝ) ^ (paperCap N - 1) =
        Real.exp (-sourceL N / (9.645908801 * Real.log (sourceL N ^ 3))) := by
      rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (nat_pos_of_exp_le hN))]
      congr 1
      dsimp [paperCap, sourceL, sourceP]
      ring
    rw [hid]
    exact paper_endpoint_decay hL
  have he32 : (N : ℝ) ^ (cap N 0.3221 - 1) ≤ 8e-18 * 3100 / sourceL N := by
    rw [cap_power_eq hN]
    have h := decay_with_seed hL (c := 0.3221) (s := 39.42) (E := 8e-18)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) exp_neg_3942
    calc
      _ ≤ 8e-18 * (3100 / sourceL N) ^ 5 := h
      _ ≤ 8e-18 * (3100 / sourceL N) :=
        mul_le_mul_of_nonneg_left (ratio_fifth_le_first hL) (by norm_num)
      _ = _ := by ring
  have he33 : 0 ≤ (N : ℝ) ^ (cap N 0.33 - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply (original_K1_small_expression hN).trans
  have hscalar : 1.0122 * (2 * (1.65e-6 * 3100) + 11 * (8e-18 * 3100)) / sourceL N ≤
      0.0104 / sourceL N := div_le_div_of_nonneg_right (by norm_num) hp.le
  calc
    _ ≤ 1.0122 * (2 * (1.65e-6 * 3100 / sourceL N) + 11 * (8e-18 * 3100 / sourceL N)) := by
      linarith
    _ = _ := by ring
    _ ≤ _ := hscalar

end LiuWang.Proof.SourceRoute.LowSum
