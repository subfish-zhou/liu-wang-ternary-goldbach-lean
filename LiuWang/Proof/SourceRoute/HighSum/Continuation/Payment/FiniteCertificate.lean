import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.RationalExp

/-! # A single explicit finite rational certificate for the original signed integral

No value of `fixedUpper` is asserted here. All transcendental rounding,
quadrature directions, and moving-domain errors are proved before that
one finite arithmetic inequality is consumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment

theorem negative_phase_bounds {A s : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1500)
    (hs : 25 ≤ s) (hs' : s ≤ 100) : 0 ≤ -phase A s ∧ -phase A s ≤ 125 := by
  have hs0 : 0 < s := by linarith
  have he : -phase A s = s + A / s := by unfold phase; ring
  rw [he]
  constructor
  · positivity
  · have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs')
    have hd : A / s ≤ 125 - s := (div_le_iff₀ hs0).mpr (by nlinarith)
    linarith

theorem negative_tangent_bounds {A m s : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1500)
    (hm : 25 ≤ m) (hm' : m ≤ 100) (hs : |s - m| ≤ 1) :
    0 ≤ -tangent A m s ∧ -tangent A m s ≤ 128 := by
  have hm0 : 0 < m := by linarith
  have hb := negative_phase_bounds hA hA' hm hm'
  have hd : 0 ≤ A / m ^ (2 : ℕ) := by positivity
  have hd' : A / m ^ (2 : ℕ) ≤ 3 := (div_le_iff₀ (pow_pos hm0 _)).mpr (by nlinarith)
  have hab : |A / m ^ (2 : ℕ) - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hh := mul_le_mul hab hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  rw [← abs_mul] at hh
  have hlow : 25 ≤ -phase A m := by
    unfold phase
    have hn : 0 ≤ A / m := by positivity
    linarith
  rcases abs_le.mp hh with ⟨hl, hu⟩
  unfold tangent
  constructor <;> linarith

def cellUpper (A u v : ℝ) : ℝ :=
  (v - u) / 2 * (expNegUpper (-tangent A ((u + v) / 2) u) +
    expNegUpper (-tangent A ((u + v) / 2) v))

def cellLower (A u v : ℝ) : ℝ :=
  (v - u) * expNegLower (-((phase A u + phase A v) / 2))

theorem rational_cell_bounds {A u v : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1500)
    (hu : 25 ≤ u) (huv : u < v) (hv : v ≤ 100) (hwidth : v - u ≤ 1) :
    cellLower A u v ≤ (∫ s in u..v, Real.exp (phase A s)) ∧
      (∫ s in u..v, Real.exp (phase A s)) ≤ cellUpper A u v := by
  have hu0 : 0 < u := by linarith
  have hm : 25 ≤ (u + v) / 2 := by linarith
  have hm' : (u + v) / 2 ≤ 100 := by linarith
  have htu := negative_tangent_bounds hA hA' hm hm'
    (s := u) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have htv := negative_tangent_bounds hA hA' hm hm'
    (s := v) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hpu := negative_phase_bounds hA hA' hu (by linarith : u ≤ 100)
  have hpv := negative_phase_bounds hA hA' (by linarith : 25 ≤ v) hv
  have hlo := (expNeg_bounds (x := -((phase A u + phase A v) / 2))
    (by linarith) (by linarith)).1
  have hhiu := (expNeg_bounds htu.1 htu.2).2
  have hhiv := (expNeg_bounds htv.1 htv.2).2
  simp only [neg_neg] at hlo hhiu hhiv
  refine ⟨?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hlo (sub_pos.mpr huv).le).trans
      (cell_exp_lower hA hu0 huv)
  · exact (cell_exp_upper hA hu0 huv).trans
      (mul_le_mul_of_nonneg_left (add_le_add hhiu hhiv) (by linarith : 0 ≤ (v - u) / 2))

def gridPoint (k : ℕ) : ℝ :=
  25329 / 1000 + (100 - 25329 / 1000) * (k : ℝ) / 512

theorem grid_cell_bounds {k : ℕ} (hk : k < 512) :
    25 ≤ gridPoint k ∧ gridPoint k < gridPoint (k + 1) ∧
      gridPoint (k + 1) ≤ 100 ∧ gridPoint (k + 1) - gridPoint k ≤ 1 := by
  have hk' : (k : ℝ) + 1 ≤ 512 := by exact_mod_cast hk
  have hk0 := Nat.cast_nonneg (α := ℝ) k
  unfold gridPoint
  push_cast
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

def quadUpper (A : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 512, cellUpper A (gridPoint k) (gridPoint (k + 1))

def quadLower (A : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 512, cellLower A (gridPoint k) (gridPoint (k + 1))

theorem quadrature_bounds {A : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1500) :
    quadLower A ≤ (∫ s in (25329 / 1000 : ℝ)..100, Real.exp (phase A s)) ∧
      (∫ s in (25329 / 1000 : ℝ)..100, Real.exp (phase A s)) ≤ quadUpper A := by
  have he := intervalIntegral.sum_integral_adjacent_intervals (a := gridPoint) (n := 512)
    (f := fun s => Real.exp (phase A s)) (μ := volume) (fun k hk =>
      exp_phase_integrable A (by linarith [(grid_cell_bounds hk).1])
        (grid_cell_bounds hk).2.1.le)
  norm_num only [gridPoint, Nat.cast_zero, mul_zero, zero_div, add_zero, Nat.cast_ofNat] at he
  norm_num at he
  have hl := Finset.sum_le_sum (s := Finset.range 512) (fun k hk =>
    (rational_cell_bounds hA hA' (grid_cell_bounds (Finset.mem_range.mp hk)).1
      (grid_cell_bounds (Finset.mem_range.mp hk)).2.1
      (grid_cell_bounds (Finset.mem_range.mp hk)).2.2.1
      (grid_cell_bounds (Finset.mem_range.mp hk)).2.2.2).1)
  have hu := Finset.sum_le_sum (s := Finset.range 512) (fun k hk =>
    (rational_cell_bounds hA hA' (grid_cell_bounds (Finset.mem_range.mp hk)).1
      (grid_cell_bounds (Finset.mem_range.mp hk)).2.1
      (grid_cell_bounds (Finset.mem_range.mp hk)).2.2.1
      (grid_cell_bounds (Finset.mem_range.mp hk)).2.2.2).2)
  change _ ≤ _ ∧ _ ≤ _
  have hsum : (∑ k ∈ Finset.range 512,
      ∫ s in gridPoint k..gridPoint (k + 1), Real.exp (phase A s)) =
      ∫ s in (25329 / 1000 : ℝ)..100, Real.exp (phase A s) := by
    convert he using 1
    norm_num [gridPoint]
  rw [hsum] at hl hu
  exact ⟨hl, hu⟩

def fixedUpper : ℝ :=
  (3100 : ℝ) ^ (4 : ℕ) *
    (35 * quadUpper 1116 + 54 * quadUpper 1209 + 93 * quadUpper 1302 +
      110 * quadUpper 1395 + 372 * quadUpper 1426 + 1004 * quadUpper 1457 +
      12332 * quadUpper (2945 / 2) - 14000 * quadLower (7409 / 5))

theorem fixed_interval_le_certificate :
    (∫ s in (25329 / 1000 : ℝ)..100, sourceIntegrand 3100 s) ≤ fixedUpper := by
  have he (s : ℝ) : sourceIntegrand 3100 s = (3100 : ℝ) ^ (4 : ℕ) *
      (35 * Real.exp (phase 1116 s) + 54 * Real.exp (phase 1209 s) +
      93 * Real.exp (phase 1302 s) + 110 * Real.exp (phase 1395 s) +
      372 * Real.exp (phase 1426 s) + 1004 * Real.exp (phase 1457 s) +
      12332 * Real.exp (phase (2945 / 2) s) - 14000 * Real.exp (phase (7409 / 5) s)) := by
    unfold sourceIntegrand source31Profile phase
    norm_num
    simp only [neg_div, Real.exp_sub, Real.exp_neg]
    ring
  have hi (A : ℝ) := exp_phase_integrable A (u := (25329 / 1000 : ℝ)) (v := 100)
    (by norm_num) (by norm_num)
  have hi12 := ((hi 1116).const_mul 35).add ((hi 1209).const_mul 54)
  have hi13 := hi12.add ((hi 1302).const_mul 93)
  have hi14 := hi13.add ((hi 1395).const_mul 110)
  have hi15 := hi14.add ((hi 1426).const_mul 372)
  have hi16 := hi15.add ((hi 1457).const_mul 1004)
  have hi17 := hi16.add ((hi (2945 / 2)).const_mul 12332)
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hi17 ((hi (7409 / 5)).const_mul 14000),
    intervalIntegral.integral_add hi16 ((hi (2945 / 2)).const_mul 12332),
    intervalIntegral.integral_add hi15 ((hi 1457).const_mul 1004),
    intervalIntegral.integral_add hi14 ((hi 1426).const_mul 372),
    intervalIntegral.integral_add hi13 ((hi 1395).const_mul 110),
    intervalIntegral.integral_add hi12 ((hi 1302).const_mul 93),
    intervalIntegral.integral_add ((hi 1116).const_mul 35) ((hi 1209).const_mul 54)]
  simp only [intervalIntegral.integral_const_mul]
  have h1 := (quadrature_bounds (A := 1116) (by norm_num) (by norm_num)).2
  have h2 := (quadrature_bounds (A := 1209) (by norm_num) (by norm_num)).2
  have h3 := (quadrature_bounds (A := 1302) (by norm_num) (by norm_num)).2
  have h4 := (quadrature_bounds (A := 1395) (by norm_num) (by norm_num)).2
  have h5 := (quadrature_bounds (A := 1426) (by norm_num) (by norm_num)).2
  have h6 := (quadrature_bounds (A := 1457) (by norm_num) (by norm_num)).2
  have h7 := (quadrature_bounds (A := 2945 / 2) (by norm_num) (by norm_num)).2
  have h8 := (quadrature_bounds (A := 7409 / 5) (by norm_num) (by norm_num)).1
  unfold fixedUpper
  nlinarith

theorem uniform_le_finite_certificate {L : ℝ} (hL : 3100 ≤ L) :
    (∫ s in lowerHeight L..upperHeight L, sourceIntegrand L s) ≤
      fixedUpper + 1 / 1000000000000000000000000000 :=
  (uniform_source31_reduction hL).trans
    (add_le_add_left (base_core_le_rational_interval.trans fixed_interval_le_certificate) _)

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment
