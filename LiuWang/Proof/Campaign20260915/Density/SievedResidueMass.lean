import LiuWang.Proof.Campaign20260915.Density.RootResidueMass
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic.QBoundary

set_option autoImplicit false
noncomputable section

open Finset
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_sqrt_boundary_scalar {X : ℝ} (hX : 100000 ≤ X) :
    1.216 * Real.sqrt X + Real.log X + 2.4 ≤ 1.261 * Real.sqrt X := by
  have hX0 : 0 < X := by linarith
  have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hb0 : 0 < Real.sqrt (100000 : ℝ) := by positivity
  have hsb : (316 : ℝ) ≤ Real.sqrt 100000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 100000)]
  have hl : Real.log (100000 : ℝ) ≤ 11.513 := by
    rw [show (100000 : ℝ) = (2 * 5) ^ 5 by norm_num,
      Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have heb : Real.exp 2 ≤ (100000 : ℝ) := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)) 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hmono := Real.log_div_sqrt_antitoneOn heb (heb.trans hX) hX
  have hinv := one_div_le_one_div_of_le hb0 (Real.sqrt_le_sqrt hX)
  have hb : (Real.log (100000 : ℝ) + 2.4) / Real.sqrt 100000 ≤ 0.045 := by
    apply (div_le_iff₀ hb0).mpr
    linarith
  have h : (Real.log X + 2.4) / Real.sqrt X ≤ 0.045 := by
    rw [add_div] at hb ⊢
    have hi := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2.4)
    simp only [mul_one_div] at hi
    linarith
  have hf := (div_le_iff₀ hs0).mp h
  linarith

theorem source_critical_coefficient_mass {X : ℝ} (hX : 100000 ≤ X) :
    (∑ n ∈ (range ⌈X⌉₊).erase 0, ‖criticalCoefficient n‖) ≤ 1.261 * Real.sqrt X := by
  have he : (∑ n ∈ (range ⌈X⌉₊).erase 0, ‖criticalCoefficient n‖) =
      ∑ n ∈ positiveBelow X, |(ArithmeticFunction.moebius n : ℝ)| / Real.sqrt n := by
    rw [strict_cutoff_eq_positiveBelow]
    exact sum_congr rfl (fun n hn => norm_criticalCoefficient (mem_positiveBelow.mp hn).1)
  rw [he]
  exact (equation_11 (by linarith)).trans (source_sqrt_boundary_scalar hX)

theorem residue_critical_mass_sieved {q N : ℕ} [NeZero q] {S : Finset ℕ}
    (hS : S ⊆ (range N).erase 0) :
    (∑ x : ZMod q, (∑ n ∈ fiber q S x, ‖criticalCoefficient n‖) ^ 2) ≤
      (2 * Real.sqrt (N / q + 1 : ℕ) / Real.sqrt q) *
        (∑ n ∈ S, ‖criticalCoefficient n‖) +
        harmonicRange q + 4 * Real.sqrt (N / q + 1 : ℕ) := by
  let K : ℕ := N / q + 1
  let C : ℝ := 2 * Real.sqrt K / Real.sqrt q
  let m (x : ZMod q) : ℝ := ∑ n ∈ fiber q S x, ‖criticalCoefficient n‖
  let a (x : ZMod q) : ℝ := (Real.sqrt x.val)⁻¹
  have hpoint (x : ZMod q) : m x ^ 2 ≤ C * m x + a x ^ 2 + C * a x := by
    have hm : 0 ≤ m x := sum_nonneg (fun _ _ => norm_nonneg _)
    have ha : 0 ≤ a x := by dsimp [a]; positivity
    have h := residue_critical_mass_le hS x
    change m x ≤ a x + C at h
    nlinarith only [mul_le_mul_of_nonneg_right h hm, mul_le_mul_of_nonneg_left h ha]
  have h := sum_le_sum (s := (univ : Finset (ZMod q))) (fun x _ => hpoint x)
  simp only [sum_add_distrib, ← mul_sum] at h
  have hm : (∑ x : ZMod q, m x) = ∑ n ∈ S, ‖criticalCoefficient n‖ := by
    dsimp [m]
    rw [sum_all_fibers]
  have ha2 : (∑ x : ZMod q, a x ^ 2) = harmonicRange q := by
    dsimp [a]
    simp_rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact sum_zmod_val q (fun n => (n : ℝ)⁻¹)
  have ha1 : (∑ x : ZMod q, a x) ≤ 2 * Real.sqrt q := by
    dsimp [a]
    rw [sum_zmod_val q (fun n => (Real.sqrt n)⁻¹)]
    exact GlobalZeroDensity.sum_inv_sqrt_le q
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hroot : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : C * (2 * Real.sqrt q) = 4 * Real.sqrt K := by
    dsimp [C]
    field_simp
    ring
  have hb := mul_le_mul_of_nonneg_left ha1 hC
  rw [he] at hb
  rw [hm, ha2] at h
  change _ ≤ C * (∑ n ∈ S, ‖criticalCoefficient n‖) + harmonicRange q + 4 * Real.sqrt K
  linarith only [h, hb]

theorem source_residue_critical_mass_sieved (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∑ x : ZMod q, (∑ n ∈ fiber q ((range ⌈(q : ℝ) * y⌉₊).erase 0) x,
      ‖criticalCoefficient n‖) ^ 2) ≤ 2.56 * y := by
  let X : ℝ := (q : ℝ) * y
  let N : ℕ := ⌈X⌉₊
  let K : ℕ := N / q + 1
  have hy' := source_height_lower (source_height_ge_log_six hy)
  have hy0 : 0 ≤ y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hX : 100000 ≤ X := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    dsimp [X]
    nlinarith only [h]
  have hN : (N : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ X)).le
  have hNq : (N : ℝ) / q ≤ y + 1 := by
    apply (div_le_iff₀ hq0).mpr
    dsimp [X] at hN
    nlinarith only [hN, hq]
  have hK : (K : ℝ) ≤ 1.001 * y := by
    have hd : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
    dsimp [K]
    push_cast
    linarith
  have hH : harmonicRange q ≤ 0.0002 * y := by
    have hlog := (max_le_iff.mp hy).2
    have h := inverse_range_le_log q
    unfold harmonicRange
    linarith
  have hs : 133 ≤ Real.sqrt y := by
    nlinarith [Real.sq_sqrt hy0, Real.sqrt_nonneg y]
  have hsqrt : Real.sqrt K ≤ 1.001 * Real.sqrt y := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hy0, Real.sq_sqrt (Nat.cast_nonneg K)]
    nlinarith
  have hsmall : 4 * Real.sqrt K ≤ 0.031 * y := by
    nlinarith [Real.sq_sqrt hy0]
  have hroot : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have he : (2 * Real.sqrt K / Real.sqrt q) * (1.261 * Real.sqrt X) =
      2.522 * Real.sqrt K * Real.sqrt y := by
    dsimp [X]
    rw [Real.sqrt_mul hq0.le]
    field_simp
    ring
  have hm := mul_le_mul_of_nonneg_left (source_critical_coefficient_mass hX)
    (show 0 ≤ 2 * Real.sqrt K / Real.sqrt q by positivity)
  rw [he] at hm
  have hm' := mul_le_mul_of_nonneg_right hsqrt
    (show 0 ≤ 2.522 * Real.sqrt y by positivity)
  have h := residue_critical_mass_sieved
    (q := q) (N := N) (S := (range N).erase 0) (Subset.refl _)
  change _ ≤ (2 * Real.sqrt K / Real.sqrt q) *
    (∑ n ∈ (range N).erase 0, ‖criticalCoefficient n‖) + harmonicRange q +
      4 * Real.sqrt K at h
  change _ ≤ 2.56 * y
  dsimp [N] at h
  nlinarith only [h, hm, hm', hH, hsmall, Real.sq_sqrt hy0]

end LiuWang.Proof.Campaign20260915.Density
