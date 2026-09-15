import LiuWang.Proof.Campaign20260915.Density.DensityScale

set_option autoImplicit false
noncomputable section

open Finset Complex
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

def horizontalEnvelope (q : ℕ) (y sigma : ℝ) : ℝ :=
  47.202 * ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - sigma) *
      Real.log ((q : ℝ) * y) ^ (6 * sigma - 2) +
    200 * Real.log ((q : ℝ) * y) ^ (4 : ℕ) * ((q : ℝ) * y) ^ (2 * (1 - sigma))

theorem horizontalEnvelope_nonneg (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (sigma : ℝ) :
    0 ≤ horizontalEnvelope q y sigma := by
  have hy0 : 0 < y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL0 : 0 < Real.log ((q : ℝ) * y) := by linarith [source_product_log_ge_eleven q hy]
  unfold horizontalEnvelope
  positivity

theorem source_maximum_left_envelope (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y a : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (ha : a ≤ 1) :
    chenMaximumBound q y a ≤
      47.202 * ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - a) *
        Real.log ((q : ℝ) * y) ^ (6 * a - 2) := by
  let V : ℝ := (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)
  let L : ℝ := Real.log ((q : ℝ) * y)
  let D : ℝ := chenPointScale q y
  have hy1 : 1 ≤ y := by linarith [source_height_ge_ten_thousand hy]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hL0 : 0 < L := by dsimp [L]; linarith [source_product_log_ge_eleven q hy]
  have hD0 : 0 < D := (show 0 < (q : ℝ) * y by positivity).trans_le
    (chen_point_scale_ge_product q hq hy1)
  have hV0 : 0 < V := by dsimp [V]; positivity
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ q))
  have hlqL : Real.log q ≤ L := Real.log_le_log hq0 (by nlinarith)
  have he : D ^ (2 : ℕ) = V * Real.log q ^ (2 : ℕ) := by
    dsimp [D, chenPointScale, V]
    simp only [mul_pow, Real.sq_sqrt hq0.le]
    ring
  have hsq : D ^ (2 : ℕ) ≤ V * L ^ (2 : ℕ) := by
    rw [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlq hlqL 2) hV0.le
  have hp := Real.rpow_le_rpow (sq_nonneg D) hsq (show 0 ≤ 1 - a by linarith)
  have hm : D ^ (2 * (1 - a)) ≤ V ^ (1 - a) * L ^ (2 * (1 - a)) := by
    rw [Real.rpow_mul hD0.le, Real.rpow_two]
    exact hp.trans_eq (by
      rw [Real.mul_rpow hV0.le (sq_nonneg L), ← Real.rpow_natCast_mul hL0.le]
      norm_num only [Nat.cast_ofNat])
  unfold chenMaximumBound
  change 47.202 * D ^ (2 * (1 - a)) * L ^ (8 * a - 4) ≤ _
  calc
    _ ≤ 47.202 * (V ^ (1 - a) * L ^ (2 * (1 - a))) * L ^ (8 * a - 4) := by gcongr
    _ = 47.202 * V ^ (1 - a) * (L ^ (2 * (1 - a)) * L ^ (8 * a - 4)) := by ring
    _ = 47.202 * V ^ (1 - a) * L ^ (6 * a - 2) := by
      rw [← Real.rpow_add hL0]
      congr 2
      ring

theorem chen_exp_four_thirds_le_four : Real.exp (4 / 3) ≤ 4 := by
  have he : Real.exp (4 / 3) ^ (2 : ℕ) = Real.exp (8 / 3) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h : Real.exp (4 / 3) ^ (2 : ℕ) ≤ (4 : ℝ) ^ (2 : ℕ) := by
    rw [he]
    linarith only [chen_exp_eight_thirds]
  exact (sq_le_sq₀ (Real.exp_pos _).le (by norm_num)).mp h

theorem source_familyMaximum_envelope (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y a b : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hab : a ≤ b) :
    familyMaximum q ((q : ℝ) * y) y a b ≤ horizontalEnvelope q y a := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let d : ℝ := sourceDelta X
  have hy' := source_height_ge_ten_thousand hy
  have hy0 : 0 < y := by linarith
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := by
    have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
    dsimp [X]
    nlinarith
  have hL := source_product_log_ge_eleven q hy
  have hL0 : 0 < L := by dsimp [L, X]; linarith
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hleft0 : 0 ≤ 47.202 * ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - a) *
      Real.log ((q : ℝ) * y) ^ (6 * a - 2) := by positivity
  have hright0 : 0 ≤ 200 * L ^ (4 : ℕ) * X ^ (2 * (1 - a)) := by positivity
  by_cases ha1 : a ≤ 1
  · exact ((source_familyMaximum_paid q hq hy ha ha1 hab).trans
      (source_maximum_left_envelope q hq hy ha1)).trans (le_add_of_nonneg_right hright0)
  have ha0 : 1 < a := lt_of_not_ge ha1
  have hright : familyMaximum q X y a b ≤ 200 * L ^ (4 : ℕ) * X ^ (2 * (1 - a)) := by
    by_cases had : a ≤ 1 + d
    · obtain ⟨sigma, hs, t, ht, he⟩ := familyMaximum_attained q X y hab
      have hm := (familySquare_le_maximum q X y
        (a := 1) (b := b) (sigma := sigma) (t := t) ⟨ha0.le.trans hs.1, hs.2⟩ ht).trans
        (source_familyMaximum_paid q hq hy (by norm_num) le_rfl (ha0.le.trans hab))
      rw [← he] at hm
      norm_num [chenMaximumBound] at hm
      have hquarter : (1 / 4 : ℝ) ≤ X ^ (2 * (1 - a)) := by
        have he : (1 / 4 : ℝ) ≤ Real.exp (-(4 / 3)) := by
          rw [Real.exp_neg, ← one_div]
          exact one_div_le_one_div_of_le (Real.exp_pos _) chen_exp_four_thirds_le_four
        apply he.trans
        rw [Real.rpow_def_of_pos hX0]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right had hL0.le
        have hs := source_shift_log q hy
        change d * L = 2 / 3 at hs
        change -(4 / 3) ≤ L * (2 * (1 - a))
        nlinarith only [hh, hs]
      have hp := mul_le_mul_of_nonneg_left hquarter (show 0 ≤ 200 * L ^ (4 : ℕ) by positivity)
      change _ ≤ 200 * L ^ (4 : ℕ) * X ^ (2 * (1 - a))
      have hm' : familyMaximum q X y a b ≤ 47.202 * L ^ (4 : ℕ) := by
        simpa only [L, X, show (47.202 : ℝ) = 23601 / 500 by norm_num] using hm
      nlinarith only [hm', hp, sq_nonneg (L ^ 2)]
    · obtain ⟨sigma, hs, t, ht, he⟩ := familyMaximum_attained q X y hab
      have hXq : 11 * (q : ℝ) ≤ X := by dsimp [X]; nlinarith
      have hmu := complete_f_point_right q hXq (show 0 < a - 1 by linarith)
        (show a - 1 ≤ 1 by linarith)
        (s := (sigma : ℂ) + t * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith [hs.1])
      have hf : familyMaximum q X y a b ≤
          1.1 * X ^ (-2 * (a - 1)) * (1 + 1 / (a - 1)) ^ 4 := by
        rw [he]
        exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hmu
      have hi := one_div_le_one_div_of_le hd (show d ≤ a - 1 by linarith)
      have hid : 1 / d = 1.5 * L := by
        dsimp only [d, sourceDelta]
        change 1 / (1 / (1.5 * L)) = _
        field_simp
      rw [hid] at hi
      have hp := pow_le_pow_left₀
        (show 0 ≤ 1 + 1 / (a - 1) by positivity)
        (show 1 + 1 / (a - 1) ≤ 1.6 * L by dsimp [L, X] at *; linarith) 4
      rw [show -2 * (a - 1) = 2 * (1 - a) by ring] at hf
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1.1 * X ^ (2 * (1 - a)) by positivity)
      nlinarith only [hf, hm, mul_nonneg (pow_nonneg hL0.le 4) (Real.rpow_nonneg hX0.le (2 * (1 - a)))]
  exact hright.trans (le_add_of_nonneg_left hleft0)

end LiuWang.Proof.Campaign20260915.Density
