import LiuWang.Proof.Campaign20260915.Density.RootResidueMass
import LiuWang.Proof.NonprincipalDensityMeans.Mollifier

set_option autoImplicit false
noncomputable section

open Finset Complex MeasureTheory Classical
open scoped ArithmeticFunction.Moebius
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance (nonprincipalCharacters)
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.ChenArithmetic

namespace LiuWang.Proof.Campaign20260915.Density

theorem complete_polynomial_mean_le (q : ℕ) [NeZero q] (S : Finset ℕ)
    (a : ℕ → ℂ) (w : ℕ → ℝ) (hw : Set.InjOn w S) {T : ℝ} (hT : 0 ≤ T) :
    (∑ chi : Character q, ∫ t in -T..T, ‖polynomial chi S a w t‖ ^ 2) / q.totient ≤
      2 * T * (∑ n ∈ S, ‖a n‖ ^ 2) +
      2 * (∑ x : ZMod q, ∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
        ‖a m‖ * ‖a n‖ / |w m - w n|) := by
  have h := familyMean_diagonal_offDiagonal q S a w hw hT
  have he : (∑ chi : Character q, ∫ t in -T..T, ‖polynomial chi S a w t‖ ^ 2) / q.totient =
      familyMean q S a w T + principalMean q S a w T := by
    unfold familyMean principalMean
    rw [← add_div]
    congr 1
    exact (sum_erase_add _ _ (mem_univ (1 : Character q))).symm
  rw [he]
  have hunit :
      (∑ x : ZMod q, if IsUnit x then
        2 * T * ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 +
        2 * ∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
          ‖a m‖ * ‖a n‖ / |w m - w n| else 0) ≤
      ∑ x : ZMod q,
        (2 * T * ∑ n ∈ fiber q S x, ‖a n‖ ^ 2 +
        2 * ∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
          ‖a m‖ * ‖a n‖ / |w m - w n|) := by
    apply sum_le_sum
    intro x _
    split_ifs
    · rfl
    · positivity
  simp only [sum_add_distrib, ← mul_sum, sum_all_fibers] at hunit
  linarith

theorem source_critical_off_diagonal (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∑ x : ZMod q, ∑ m ∈ fiber q ((range ⌈(q : ℝ) * y⌉₊).erase 0) x,
      ∑ n ∈ (fiber q ((range ⌈(q : ℝ) * y⌉₊).erase 0) x).erase m,
        ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ / |Real.log m - Real.log n|) ≤
      (5 / 4) * y * Real.log y + 2.1 * y := by
  let X : ℝ := (q : ℝ) * y
  let S : Finset ℕ := (range ⌈X⌉₊).erase 0
  have hylog := source_height_ge_log_six hy
  have hy' : 10000 ≤ y := by linarith [(source_height_log_bounds hylog).1]
  have hy0 : 0 ≤ y := by linarith
  have hLy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hXy : y ≤ X := by dsimp [X]; nlinarith
  have hp (x : ZMod q) (n : ℕ) (hn : n ∈ fiber q S x) : 0 < n :=
    Nat.pos_of_ne_zero (mem_erase.mp (mem_filter.mp hn).1).1
  have hrow (x : ZMod q) (m : ℕ) (hm : m ∈ fiber q S x) :
      (∑ n ∈ (fiber q S x).erase m, |(μ m : ℝ)| / |(m : ℝ) - n|) ≤
        (2 / q) * Real.log y * |(μ m : ℝ)| := by
    calc
      _ ≤ ∑ n ∈ fiber q S x, |(μ m : ℝ)| / |(m : ℝ) - n| :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
      _ = |(μ m : ℝ)| * ∑ n ∈ fiber q S x, 1 / |(m : ℝ) - n| := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ => by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (source_congruence_gap_row hy' (erase_subset _ _) x hm) (abs_nonneg _)).trans_eq (by ring)
  have hsmooth (x : ZMod q) :
      (∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
        (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖) ≤
        (1 / 2) * (∑ n ∈ fiber q S x, ‖criticalCoefficient n‖) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ fiber q S x, ∑ n ∈ fiber q S x,
          (1 / 2) * ‖criticalCoefficient m‖ * ‖criticalCoefficient n‖ := by
        exact sum_le_sum (fun _ _ =>
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity))
      _ = _ := by simp only [← mul_sum, ← sum_mul]; ring
  have hpoint := sum_le_sum (s := (univ : Finset (ZMod q))) (fun x _ =>
    sum_le_sum (fun m hm => sum_le_sum (fun n hn =>
      weighted_coefficient_gap (hp x m hm) (hp x n (mem_erase.mp hn).2) (mem_erase.mp hn).1.symm)))
  simp only [sum_add_distrib] at hpoint
  have hnear := sum_le_sum (s := (univ : Finset (ZMod q))) (fun x _ =>
    sum_le_sum (fun m hm => hrow x m hm))
  simp only [← mul_sum, sum_all_fibers] at hnear
  have hcount : (∑ m ∈ S, |(μ m : ℝ)|) = squarefreeCount X := by
    rw [show S = positiveBelow X from strict_cutoff_eq_positiveBelow X]
    rfl
  rw [hcount] at hnear
  have hcountB := mul_le_mul_of_nonneg_left (squarefree_count_budget (hylog.trans hXy))
    (show 0 ≤ (2 / (q : ℝ)) * Real.log y by positivity)
  have hcountE : (2 / (q : ℝ)) * Real.log y * ((5 / 8) * X) =
      (5 / 4) * y * Real.log y := by dsimp [X]; field_simp; ring
  rw [hcountE] at hcountB
  have hsm := sum_le_sum (s := (univ : Finset (ZMod q))) (fun x _ => hsmooth x)
  rw [← mul_sum] at hsm
  have hmass := mul_le_mul_of_nonneg_left (source_residue_critical_mass_square q hy)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  dsimp [S, X] at hpoint hnear hsm
  nlinarith only [hpoint, hnear, hcountB, hsm, hmass]

theorem complete_Q_mean_prebudget (q : ℕ) [NeZero q] {y u : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) (hu : 0 ≤ u) :
    (∑ chi : Character q, ∫ t in -(y * u)..y * u,
      ‖NonprincipalDensityAdvance.Q chi ((q : ℝ) * y) ((1 / 2 : ℂ) + t * I)‖ ^ 2) ≤
      (q.totient : ℝ) * y *
        (2 * u * (Real.log ((q : ℝ) * y) + 0.7) + 2.5 * Real.log y + 4.2) := by
  let X : ℝ := (q : ℝ) * y
  let S : Finset ℕ := (range ⌈X⌉₊).erase 0
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 ≤ y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX : 10000 ≤ X := by dsimp [X]; nlinarith
  have hp (n : ℕ) (hn : n ∈ S) : 0 < n := Nat.pos_of_ne_zero (mem_erase.mp hn).1
  have hw : Set.InjOn (fun n : ℕ => -Real.log n) S := by
    intro m hm n hn he
    have h := congrArg Real.exp (neg_injective he)
    rw [Real.exp_log (Nat.cast_pos.mpr (hp m hm)),
      Real.exp_log (Nat.cast_pos.mpr (hp n hn))] at h
    exact_mod_cast h
  have h := complete_polynomial_mean_le q S criticalCoefficient (fun n => -Real.log n) hw
    (mul_nonneg hy0 hu)
  have he (m n : ℕ) : |-Real.log m - -Real.log n| = |Real.log m - Real.log n| := by
    rw [neg_sub_neg, abs_sub_comm]
  simp_rw [he] at h
  have hdiag := (criticalCoefficient_energy_le ⌈X⌉₊).trans (harmonic_cutoff_budget hX)
  have hd := mul_le_mul_of_nonneg_left hdiag (show 0 ≤ 2 * (y * u) by positivity)
  have hoff := source_critical_off_diagonal q hy
  have hnorm : (∑ chi : Character q, ∫ t in -(y * u)..y * u,
      ‖polynomial chi S criticalCoefficient (fun n => -Real.log n) t‖ ^ 2) / q.totient ≤
      y * (2 * u * (Real.log X + 0.7) + 2.5 * Real.log y + 4.2) := by
    dsimp [S, X] at h hd
    dsimp [X]
    nlinarith only [h, hd, hoff]
  have hphi : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hraw := (div_le_iff₀ hphi).mp hnorm
  simp_rw [Q_critical_eq_wave]
  exact hraw.trans_eq (by dsimp [X]; ring)

#print axioms complete_Q_mean_prebudget

end LiuWang.Proof.Campaign20260915.Density
