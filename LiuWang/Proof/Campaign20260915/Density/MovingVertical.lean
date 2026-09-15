import LiuWang.Proof.Campaign20260915.Density.Equation32

set_option autoImplicit false
noncomputable section

open Complex MeasureTheory
open LiuWang.Proof.DirichletZeroCount.Applications
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.Density

def chenDensityScale (q : ℕ) (y alpha : ℝ) : ℝ :=
  ((q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)) ^ (1 - alpha) *
    Real.log ((q : ℝ) * y) ^ (6 * alpha)

theorem chen_vertical_constant :
    1.272 * 42.6154 * 30.5879 * Real.exp (8 / 3) * 3 / (4 * Real.pi) ≤ 5698 := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
  nlinarith only [chen_exp_eight_thirds, Real.pi_gt_d4.le]

theorem source_vertical_main_scalar (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ alpha) (ha1 : alpha ≤ 1) :
    (1.272 * chenInterpolatedBound q y (alpha - sourceDelta ((q : ℝ) * y))) /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 5698 * chenDensityScale q y alpha := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let d : ℝ := sourceDelta X
  let V : ℝ := (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ)
  have hy0 : 0 < y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hL := source_product_log_ge_eleven q hy
  have hL0 : 0 < L := by dsimp [L, X]; linarith
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hV : 0 < V := by dsimp [V]; positivity
  have heV : X ^ (3 : ℕ) * y = V := by dsimp [X, V]; ring
  have hlogy : Real.log y ≤ L := Real.log_le_log hy0 (by dsimp [X]; nlinarith)
  have hdL : d * L = 2 / 3 := by
    dsimp only [d, sourceDelta]
    change 1 / (1.5 * L) * L = _
    field_simp
    norm_num
  have hlogV : Real.log V ≤ 4 * L := by
    rw [← heV, Real.log_mul (by positivity) hy0.ne', Real.log_pow]
    change 3 * L + Real.log y ≤ _
    linarith
  have hVd : V ^ d ≤ Real.exp (8 / 3) := by
    rw [Real.rpow_def_of_pos hV]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlogV hd.le, hdL]
  have hmoving : V ^ (1 - (alpha - d)) ≤ V ^ (1 - alpha) * Real.exp (8 / 3) := by
    rw [show 1 - (alpha - d) = (1 - alpha) + d by ring, Real.rpow_add hV]
    exact mul_le_mul_of_nonneg_left hVd (by positivity)
  have hlogpower : L ^ (6 * (alpha - d) - 1) * L ≤ L ^ (6 * alpha) := by
    calc
      _ = L ^ (6 * (alpha - d) - 1) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L ^ (6 * (alpha - d)) := by rw [← Real.rpow_add hL0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by dsimp [L, X]; linarith) (by linarith)
  have hbase : (30.5879 : ℝ) ^ (alpha - d) ≤ 30.5879 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 30.5879) (show alpha - d ≤ 1 by linarith)
  have hinv : 1 / (2 * Real.pi * d) = 3 * L / (4 * Real.pi) := by
    dsimp only [d, sourceDelta]
    change 1 / (2 * Real.pi * (1 / (1.5 * L))) = _
    field_simp
    ring
  have he : (1.272 * chenInterpolatedBound q y (alpha - d)) / (2 * Real.pi * d) =
      (1.272 * 42.6154 * (30.5879 : ℝ) ^ (alpha - d) * (3 / (4 * Real.pi))) *
        V ^ (1 - (alpha - d)) * (L ^ (6 * (alpha - d) - 1) * L) := by
    unfold chenInterpolatedBound
    change (1.272 * (42.6154 * (30.5879 : ℝ) ^ (alpha - d) *
      (X ^ (3 : ℕ) * y) ^ (1 - (alpha - d)) * L ^ (6 * (alpha - d) - 1))) /
        (2 * Real.pi * d) = _
    rw [heV, div_eq_mul_inv, ← one_div, hinv]
    ring
  rw [he]
  calc
    _ ≤ (1.272 * 42.6154 * 30.5879 * (3 / (4 * Real.pi))) *
        (V ^ (1 - alpha) * Real.exp (8 / 3)) * L ^ (6 * alpha) := by
      gcongr
    _ = (1.272 * 42.6154 * 30.5879 * Real.exp (8 / 3) * 3 / (4 * Real.pi)) *
        (V ^ (1 - alpha) * L ^ (6 * alpha)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right chen_vertical_constant (by positivity)

theorem source_vertical_main_paid (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ alpha) (ha1 : alpha ≤ 1) :
    familyMean q ((q : ℝ) * y) (alpha - sourceDelta ((q : ℝ) * y)) y /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 5698 * chenDensityScale q y alpha := by
  have hd := (source_product_shift_bounds q hy).1
  have hmean := source_familyMean_equation_32 q hy
    (sigma := alpha - sourceDelta ((q : ℝ) * y)) ⟨by linarith, by linarith⟩
  exact (div_le_div_of_nonneg_right hmean (by positivity)).trans
    (source_vertical_main_scalar q hy ha ha1)

theorem log_le_half_sub_one {X : ℝ} (hX : 4 ≤ X) : Real.log X ≤ (X - 1) / 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < X / 4 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have h4 : Real.log 4 ≤ 1.5 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  linarith

theorem source_vertical_right_paid (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (3 / 2) * familyMean q ((q : ℝ) * y) 2 y /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 2 := by
  let X : ℝ := (q : ℝ) * y
  let L : ℝ := Real.log X
  let d : ℝ := sourceDelta X
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX : 100000 ≤ X := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    dsimp [X]
    nlinarith only [h]
  have hy0 : 0 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hXm : 0 < X - 1 := by linarith
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hden : 0 < 2 * Real.pi * d := by positivity
  have hphi : ((q.totient - 1 : ℕ) : ℝ) ≤ q :=
    Nat.cast_le.mpr ((Nat.sub_le _ _).trans (Nat.totient_le q))
  have hm := mul_le_mul_of_nonneg_left (familyMean_two_le q (X := X) (by linarith) hy0)
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  have hp := mul_le_mul_of_nonneg_left hphi
    (show 0 ≤ 12 * y / (X - 1) ^ 2 by positivity)
  have hraw : (3 / 2) * familyMean q X 2 y ≤ 12 * X / (X - 1) ^ 2 := by
    dsimp [X] at hm hp ⊢
    simp only [div_eq_mul_inv] at hm hp ⊢
    nlinarith only [hm, hp]
  have hinv : 1 / (2 * Real.pi * d) = 3 * L / (4 * Real.pi) := by
    dsimp only [d, sourceDelta]
    change 1 / (2 * Real.pi * (1 / (1.5 * L))) = _
    field_simp
    ring
  have he : (12 * X / (X - 1) ^ 2) / (2 * Real.pi * d) =
      9 * X * L / (Real.pi * (X - 1) ^ 2) := by
    rw [div_eq_mul_inv _ (2 * Real.pi * d), ← one_div (2 * Real.pi * d), hinv]
    field_simp
    ring
  have hb : 9 * X * L / (Real.pi * (X - 1) ^ 2) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi * (X - 1) ^ 2)).mpr
    have hl := mul_le_mul_of_nonneg_left (log_le_half_sub_one (by linarith : 4 ≤ X))
      (show 0 ≤ 9 * X by linarith)
    have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg (X - 1))
    have hx := mul_nonneg (show 0 ≤ X - 1 by linarith) (show 0 ≤ X - 4 by linarith)
    change 9 * X * L ≤ _
    dsimp [L] at *
    nlinarith only [hl, hp, hx]
  exact ((div_le_div_of_nonneg_right hraw hden.le).trans_eq he).trans hb

theorem source_vertical_density_paid (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ alpha) (ha1 : alpha ≤ 1) :
    (familyMean q ((q : ℝ) * y) (alpha - sourceDelta ((q : ℝ) * y)) y +
      (3 / 2) * familyMean q ((q : ℝ) * y) 2 y) /
        (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 5700 * chenDensityScale q y alpha := by
  have hd := source_product_shift_bounds q hy
  have hy' : 1 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hL := source_product_log_ge_eleven q hy
  have hV : 1 ≤ (q : ℝ) ^ (3 : ℕ) * y ^ (4 : ℕ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) (one_le_pow₀ hy')
  have hscale : 1 ≤ chenDensityScale q y alpha := by
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hV (by linarith))
      (Real.one_le_rpow (by linarith : 1 ≤ Real.log ((q : ℝ) * y)) (by linarith [hd.1]))
  rw [add_div]
  have hm := source_vertical_main_paid q hy ha ha1
  have hr := source_vertical_right_paid q hy
  nlinarith only [hm, hr, hscale]

theorem source_product_vertical_integrals_paid (q : ℕ) [NeZero q] {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ alpha) (ha1 : alpha ≤ 1) :
    ((∫ t in -y..y, Real.log ‖familyProduct q ((q : ℝ) * y)
      (((alpha - sourceDelta ((q : ℝ) * y) : ℝ) : ℂ) + t * I)‖) -
      (∫ t in -y..y, Real.log ‖familyProduct q ((q : ℝ) * y) ((2 : ℂ) + t * I)‖)) /
        (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤ 5700 * chenDensityScale q y alpha := by
  have hy0 : 0 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX : 5 ≤ (q : ℝ) * y := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    nlinarith only [h]
  have hd := (source_product_shift_bounds q hy).1
  have h := add_le_add
    (product_left_integral q ((q : ℝ) * y) (alpha - sourceDelta ((q : ℝ) * y)) hy0)
    (product_right_integral q hX hy0)
  rw [← sub_eq_add_neg] at h
  exact (div_le_div_of_nonneg_right h (by positivity)).trans
    (source_vertical_density_paid q hy ha ha1)

#print axioms source_vertical_density_paid
#print axioms source_product_vertical_integrals_paid

end LiuWang.Proof.Campaign20260915.Density
