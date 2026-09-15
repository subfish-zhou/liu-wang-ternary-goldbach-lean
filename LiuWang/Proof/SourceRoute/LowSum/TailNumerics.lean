import LiuWang.Proof.SourceRoute.LowSum.TailIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.LowSum

def seedExp (a : ℝ) : ℝ := Real.exp (-a * seedRatio)

theorem seed_enclosure {a l u xl xu : ℝ} (n : ℕ)
    (hxl : 0 ≤ xl) (hxu : 0 ≤ xu) (hxu1 : xu ≤ 1)
    (hslo : n + xl ≤ a * seedRatio) (hshi : a * seedRatio ≤ n + xu)
    (hu : 0 < u)
    (hlo : (2.7182818286 : ℝ) ^ n *
      ((∑ i ∈ Finset.range 9, xu ^ i / i.factorial) +
        xu ^ 9 * (9 + 1) / ((9 : ℕ).factorial * 9)) ≤ 1 / l)
    (hhi : 1 / u ≤ (2.7182818283 : ℝ) ^ n *
      (∑ i ∈ Finset.range 9, xl ^ i / i.factorial)) :
    l ≤ seedExp a ∧ seedExp a ≤ u := by
  have hupper : Real.exp (a * seedRatio) ≤ 1 / l := by
    calc
      _ ≤ Real.exp (n + xu) := Real.exp_le_exp.mpr hshi
      _ = Real.exp 1 ^ n * Real.exp xu := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        simp only [mul_one]
      _ ≤ (2.7182818286 : ℝ) ^ n *
        ((∑ i ∈ Finset.range 9, xu ^ i / i.factorial) +
          xu ^ 9 * (9 + 1) / ((9 : ℕ).factorial * 9)) :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n)
          (Real.exp_bound' hxu hxu1 (by norm_num : 0 < (9 : ℕ)))
          (Real.exp_pos _).le (by positivity)
      _ ≤ _ := hlo
  have hlower : 1 / u ≤ Real.exp (a * seedRatio) := by
    calc
      _ ≤ (2.7182818283 : ℝ) ^ n *
          (∑ i ∈ Finset.range 9, xl ^ i / i.factorial) := hhi
      _ ≤ Real.exp 1 ^ n * Real.exp xl :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n)
          (Real.sum_le_exp_of_nonneg hxl 9) (by positivity) (by positivity)
      _ = Real.exp (n + xl) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        simp only [mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hslo
  unfold seedExp
  rw [show -a * seedRatio = -(a * seedRatio) by ring, Real.exp_neg]
  constructor
  · have h := one_div_le_one_div_of_le (Real.exp_pos _) hupper
    simpa only [one_div, inv_inv] using h
  · have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / u) hlower
    simpa only [one_div, inv_inv] using h

theorem seed_0478 : 3.919e-26 ≤ seedExp 0.478 ∧ seedExp 0.478 ≤ 3.921e-26 := by
  apply seed_enclosure (n := 58) (xl := 0.5011) (xu := 0.5012) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_0475 : 5.658e-26 ≤ seedExp 0.475 ∧ seedExp 0.475 ≤ 5.660e-26 := by
  apply seed_enclosure (n := 58) (xl := 0.1339) (xu := 0.1340) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_047 : 1.043e-25 ≤ seedExp 0.47 ∧ seedExp 0.47 ≤ 1.044e-25 := by
  apply seed_enclosure (n := 57) (xl := 0.5220) (xu := 0.5221) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_046 : 3.548e-25 ≤ seedExp 0.46 ∧ seedExp 0.46 ≤ 3.550e-25 := by
  apply seed_enclosure (n := 56) (xl := 0.2981) (xu := 0.2982) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_045 : 1.206e-24 ≤ seedExp 0.45 ∧ seedExp 0.45 ≤ 1.207e-24 := by
  apply seed_enclosure (n := 55) (xl := 0.0742) (xu := 0.0743) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_042 : 4.743e-23 ≤ seedExp 0.42 ∧ seedExp 0.42 ≤ 4.745e-23 := by
  apply seed_enclosure (n := 51) (xl := 0.4026) (xu := 0.4027) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_039 : 1.864e-21 ≤ seedExp 0.39 ∧ seedExp 0.39 ≤ 1.866e-21 := by
  apply seed_enclosure (n := 47) (xl := 0.7310) (xu := 0.7311) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_036 : 7.331e-20 ≤ seedExp 0.36 ∧ seedExp 0.36 ≤ 7.334e-20 := by
  apply seed_enclosure (n := 44) (xl := 0.0594) (xu := 0.0595) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_033 : 2.882e-18 ≤ seedExp 0.33 ∧ seedExp 0.33 ≤ 2.884e-18 := by
  apply seed_enclosure (n := 40) (xl := 0.3878) (xu := 0.3879) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem seed_032 : 9.801e-18 ≤ seedExp 0.32 ∧ seedExp 0.32 ≤ 9.804e-18 := by
  apply seed_enclosure (n := 39) (xl := 0.1639) (xu := 0.1640) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem segment_paid {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a b D C U E : ℝ} (hU : seedExp b ≤ U) (hE : E ≤ seedExp a)
    (hb : 0.1 ≤ b) (hba : b ≤ a) (ha : a ≤ 0.478) (hD : 0 ≤ D)
    (hcost : D * 1.0193 * (25.32942 / 25.3294) * 3100 * (U - E) ≤ C) :
    (∫ alpha in cap N a..cap N b, D * kernel N alpha) ≤ C / sourceL N := by
  apply (original_segment_integral_le hN hb hba ha hD).trans
  apply div_le_div_of_nonneg_right _ (by linarith [sourceL_ge_3100 hN])
  have hd : seedExp b - seedExp a ≤ U - E := by linarith
  exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans hcost

theorem original_211 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.478..cap N 0.475, 14000 * kernel N alpha) ≤ 2e-18 / sourceL N := by
  apply segment_paid hN seed_0475.2 seed_0478.1 <;> norm_num

theorem original_212a {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.475..cap N 0.47, 1668 * kernel N alpha) ≤ 6e-19 / sourceL N := by
  apply segment_paid hN seed_047.2 seed_0475.1 <;> norm_num

theorem original_212b {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.47..cap N 0.46, 664 * kernel N alpha) ≤ 2e-18 / sourceL N := by
  apply segment_paid hN seed_046.2 seed_047.1 <;> norm_num

theorem original_212c {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.46..cap N 0.45, 292 * kernel N alpha) ≤ 2e-18 / sourceL N := by
  apply segment_paid hN seed_045.2 seed_046.1 <;> norm_num

theorem original_212d {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.45..cap N 0.42, 182 * kernel N alpha) ≤ 6e-17 / sourceL N := by
  apply segment_paid hN seed_042.2 seed_045.1 <;> norm_num

theorem original_212e {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.42..cap N 0.39, 89 * kernel N alpha) ≤ 6e-16 / sourceL N := by
  apply segment_paid hN seed_039.2 seed_042.1 <;> norm_num

theorem original_212f {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.39..cap N 0.36, 35 * kernel N alpha) ≤ 8e-15 / sourceL N := by
  apply segment_paid hN seed_036.2 seed_039.1 <;> norm_num

theorem original_212g {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.36..cap N 0.33, 20 * kernel N alpha) ≤ 2e-13 / sourceL N := by
  apply segment_paid hN seed_033.2 seed_036.1 <;> norm_num

theorem original_212h {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    (∫ alpha in cap N 0.33..cap N 0.32, 13 * kernel N alpha) ≤ 3e-13 / sourceL N := by
  apply segment_paid hN seed_032.2 seed_033.1 <;> norm_num

end LiuWang.Proof.SourceRoute.LowSum
