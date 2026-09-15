import LiuWang.Proof.WeightedHighZeros.Continuation.Frontier.Consumer
import LiuWang.Proof.DirichletZeroCount.Remainder.SourceFamily

/-! # Admitted uniform counts on dyadic bands starting at the original omega -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Remainder

namespace LiuWang.Proof.WeightedHighZeros.Continuation.Frontier

theorem log_product_ge_one {q : ℕ} [NeZero q] {y : ℝ} (hy : 4 ≤ y) :
    1 ≤ Real.log ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  exact Real.exp_one_lt_three.le.trans
    ((by linarith : (3 : ℝ) ≤ y).trans (le_mul_of_one_le_left (by linarith) hq))

theorem log_shift_le_four {q : ℕ} [NeZero q] {y c : ℝ}
    (hy : 4 ≤ y) (hc : 0 ≤ c) (hc4 : c ≤ 4) :
    Real.log (y + c) ≤ Real.log ((q : ℝ) * y) + 1 := by
  have hh := Real.log_le_log (by linarith : 0 < y + c)
    (by linarith : y + c ≤ 2 * y)
  rw [Real.log_mul (by norm_num) (by linarith : y ≠ 0)] at hh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hly := Real.log_le_log (by linarith : 0 < y)
    (le_mul_of_one_le_left (by linarith : 0 ≤ y) hq)
  linarith

theorem nonprincipal_four_le_ten {q : ℕ} [NeZero q] {y : ℝ} (hy : 4 ≤ y) :
    nonprincipalBound q y ≤ 10 * y * Real.log ((q : ℝ) * y) := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hS := log_product_ge_one (q := q) hy
  have hlq : Real.log q ≤ Real.log ((q : ℝ) * y) :=
    Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) (by linarith))
  have hls := log_shift_le_four (q := q) hy (c := 3) (by norm_num) (by norm_num)
  have hb : Real.log q / 2 + Real.log (y + 3) / 2 + 5 / 4 ≤
      3 * Real.log ((q : ℝ) * y) := by linarith
  have hb0 : 0 ≤ Real.log q / 2 + Real.log (y + 3) / 2 + 5 / 4 := by
    have h1 := Real.log_nonneg hq
    have h2 := Real.log_nonneg (by linarith : 1 ≤ y + 3)
    linarith
  calc
    _ ≤ (3 * y) * (3 * Real.log ((q : ℝ) * y)) :=
      mul_le_mul (by linarith) hb hb0 (by linarith)
    _ ≤ _ := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ y)
        (by linarith : 0 ≤ Real.log ((q : ℝ) * y))]

theorem principal_four_le_ten {q : ℕ} [NeZero q] {y : ℝ} (hy : 4 ≤ y) :
    principalBound y ≤ 10 * y * Real.log ((q : ℝ) * y) := by
  have hS := log_product_ge_one (q := q) hy
  have hls := log_shift_le_four (q := q) hy (c := 4) (by norm_num) (by norm_num)
  have hi : 1 / (y + 3) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hb : Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3 ≤
      3 * Real.log ((q : ℝ) * y) := by linarith
  have hb0 : 0 ≤ Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3 := by
    have h := Real.log_nonneg (by linarith : 1 ≤ y + 4)
    positivity
  calc
    _ ≤ (2 * y + 4) * (Real.log (y + 4) / 2 + 1 / (y + 3) + 1 / 3) := by
      rw [principalBound, if_neg (by linarith)]
      exact min_le_right _ _
    _ ≤ (3 * y) * (3 * Real.log ((q : ℝ) * y)) :=
      mul_le_mul (by linarith) hb hb0 (by linarith)
    _ ≤ _ := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ y)
        (by linarith : 0 ≤ Real.log ((q : ℝ) * y))]

theorem uniformFamilyBound_le_familyBound (q : ℕ) [NeZero q] (y : ℝ) :
    uniformFamilyBound q y ≤ familyBound q y := by
  exact add_le_add (min_le_left _ _)
    (Finset.sum_le_sum (fun _ _ => min_le_left _ _))

theorem uniform_four_le_ten (q : ℕ) [NeZero q] {y : ℝ} (hy : 4 ≤ y) :
    uniformFamilyBound q y ≤ 10 * q * y * Real.log ((q : ℝ) * y) := by
  have hphi : 1 ≤ q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  have hcast : ((q.totient - 1 : ℕ) : ℝ) + 1 = q.totient := by
    exact_mod_cast Nat.sub_add_cancel hphi
  have hS := log_product_ge_one (q := q) hy
  have hB : 0 ≤ 10 * y * Real.log ((q : ℝ) * y) := by positivity
  calc
    _ ≤ principalBound y + (q.totient - 1 : ℕ) * nonprincipalBound q y :=
      (uniformFamilyBound_le_familyBound q y).trans (familyBound_le_modulus q (by linarith))
    _ ≤ 10 * y * Real.log ((q : ℝ) * y) +
        (q.totient - 1 : ℕ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      add_le_add (principal_four_le_ten hy)
        (mul_le_mul_of_nonneg_left (nonprincipal_four_le_ten hy) (Nat.cast_nonneg _))
    _ = q.totient * (10 * y * Real.log ((q : ℝ) * y)) := by rw [← hcast]; ring
    _ ≤ (q : ℝ) * (10 * y * Real.log ((q : ℝ) * y)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le q)) hB
    _ = _ := by ring

def uniformShell (q : ℕ) [NeZero q] (u y : ℝ) : ℝ := uniformFamilyBound q y / u

def uniformGeometric (q : ℕ) [NeZero q] (u : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), uniformShell q ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u)

theorem reciprocal_band_le_uniform {q : ℕ} [NeZero q] {u y : ℝ}
    (hu : 0 < u) (hy : 0 ≤ y) :
    bandSum 1 q u y ≤ uniformShell q u y := by
  have hh := family_band_weighted_le_uniform q (alpha := 1 / 2) (by norm_num) hy u
    (fun _ rho => 1 / |rho.im|) (M := 1 / u) (by positivity)
    (fun _ _ hr => one_div_le_one_div_of_le hu (mem_bandValues.mp hr).2.2.2)
  simpa only [bandSum, Nat.cast_one, Real.one_rpow, uniformShell, one_div_mul_eq_div] using hh

theorem reciprocal_band_le_uniformGeometric {q : ℕ} [NeZero q] {u : ℝ}
    (hu : 0 < u) (k : ℕ) :
    bandSum 1 q u ((2 : ℝ) ^ (k + 1) * u) ≤ uniformGeometric q u k := by
  induction k with
  | zero =>
    simpa [uniformGeometric] using reciprocal_band_le_uniform (q := q) hu
      (show 0 ≤ 2 * u by positivity)
  | succ k ih =>
    have hh := reciprocal_band_le_uniform (q := q)
      (show 0 < (2 : ℝ) ^ (k + 1) * u by positivity)
      (show 0 ≤ (2 : ℝ) ^ (k + 1 + 1) * u by positivity)
    have hs := (bandSum_split_le 1 q u ((2 : ℝ) ^ (k + 1) * u)
      ((2 : ℝ) ^ (k + 1 + 1) * u)).trans (add_le_add ih hh)
    simpa only [uniformGeometric, Finset.sum_range_succ] using hs

def uniformReciprocal (N q : ℕ) [NeZero q] : ℝ :=
  min (uniformShell q (omegaCutoff N q) (sourceT N))
    (uniformGeometric q (omegaCutoff N q) (coverIndex (omegaCutoff N q) (sourceT N) 2))

theorem actual_reciprocal_le_uniform {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) :
    bandSum 1 q (omegaCutoff N q) (sourceT N) ≤ uniformReciprocal N q := by
  have hn := Parameters.exp_2000_le_of_exp_3100_le hN
  have hu := Parameters.omegaCutoff_pos hn (NeZero.pos q)
  have ht := Parameters.sourceT_pos hn
  exact le_min (reciprocal_band_le_uniform hu ht.le)
    ((bandSum_mono_height 1 q (omegaCutoff N q)
      (height_le_cover hu ht (by norm_num : (1 : ℝ) < 2))).trans
        (reciprocal_band_le_uniformGeometric hu _))

theorem uniformShell_le_source (q : ℕ) [NeZero q] {u y : ℝ}
    (hu : 0 ≤ u) (hy : 0 ≤ y) :
    uniformShell q u y ≤ sourceFamilyBound q y / u :=
  div_le_div_of_nonneg_right (uniformFamilyBound_le_source q hy) hu

end LiuWang.Proof.WeightedHighZeros.Continuation.Frontier
