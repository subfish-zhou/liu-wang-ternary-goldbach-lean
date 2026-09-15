import LiuWang.Proof.Campaign20260915.Density.ResidueKernel

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory
open LiuWang.Proof.NonprincipalDensityMeans
open LiuWang.Proof.GlobalZeroDensity.Sharp

namespace LiuWang.Proof.Campaign20260915.Density

theorem family_right_finite_mean {q : ℕ} [NeZero q] {S : Finset ℕ}
    {X d T : ℝ} (hX : 2 * (q : ℝ) ≤ X) (hd : 0 < d) (hd1 : d ≤ 1)
    (hS : ∀ n ∈ S, X ≤ (n : ℝ)) (hT : 0 ≤ T) :
    familyMean q S (rightTerm X (1 + d)) (fun n => -Real.log n) T ≤
      2 * T * ((24 / X) * X ^ (-2 * d)) +
      (4 / q) * (3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4) +
      (8 / q) * X ^ (-d) * (1 + 1 / d) ^ 5 := by
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX1 : 1 < X := by linarith
  have hp (n : ℕ) (hn : n ∈ S) : 0 < n := by
    have : (0 : ℝ) < n := by linarith [hS n hn]
    exact_mod_cast this
  let A := fun n => ‖rightTerm X (1 + d) n‖
  have hw : Set.InjOn (fun n : ℕ => -Real.log n) S := by
    intro m hm n hn he
    have hh := Real.log_injOn_pos
      (show (m : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < m; exact_mod_cast hp m hm)
      (show (n : ℝ) ∈ Set.Ioi 0 by change (0 : ℝ) < n; exact_mod_cast hp n hn)
      (neg_injective he)
    exact_mod_cast hh
  have habs (m n : ℕ) :
      |-Real.log m - -Real.log n| = |Real.log m - Real.log n| := by
    rw [neg_sub_neg, abs_sub_comm]
  have hm := (familyMean_diagonal_offDiagonal q S (rightTerm X (1 + d))
    (fun n => -Real.log n) hw hT).trans
    (sub_le_self _ (principalMean_nonneg q S (rightTerm X (1 + d))
      (fun n => -Real.log n) hT))
  simp_rw [habs] at hm
  have hunit :
      (∑ x : ZMod q, if IsUnit x then
        2 * T * ∑ n ∈ fiber q S x, A n ^ 2 +
        2 * ∑ m ∈ fiber q S x, ∑ n ∈ (fiber q S x).erase m,
          A m * A n / |Real.log m - Real.log n| else 0) ≤
      ∑ x : ZMod q,
        (2 * T * ∑ n ∈ fiber q S x, A n ^ 2 +
        2 * ∑ m ∈ fiber q S x, ∑ n ∈ fiber q S x,
          A m * A n / |Real.log m - Real.log n|) := by
    apply sum_le_sum
    intro x _
    split_ifs
    · apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum (fun _ _ => sum_le_sum_of_subset_of_nonneg
        (erase_subset _ _) (fun _ _ _ => by dsimp [A]; positivity))
    · dsimp [A]
      positivity
  have hm' := hm.trans hunit
  simp only [sum_add_distrib, ← mul_sum, sum_all_fibers] at hm'
  have hk := sum_le_sum (fun x (_hx : x ∈ (univ : Finset (ZMod q))) =>
    residue_weighted_off_diagonal S hp x A (fun _ _ => norm_nonneg _))
  simp only [sum_add_distrib, ← mul_sum, sum_all_fibers] at hk
  have hmass := sum_le_sum (fun x (_hx : x ∈ (univ : Finset (ZMod q))) =>
    residue_rightTerm_mass x hX hd hd1 hS)
  simp only [← mul_sum, sum_all_fibers] at hmass
  have hE := divisor_square_power hp (show 1 < 1 + d by linarith)
  simp only [add_sub_cancel_left] at hE
  have hmass' := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ (2 / q) * X ^ (-d) * (1 + 1 / d) by positivity)
  have heMass : ((2 / (q : ℝ)) * X ^ (-d) * (1 + 1 / d)) *
      (1 + 1 / d) ^ 4 = (2 / q) * X ^ (-d) * (1 + 1 / d) ^ 5 := by ring
  rw [heMass] at hmass'
  have hlog := mul_le_mul_of_nonneg_left (rightTerm_log_moment hp hX1 hd)
    (show 0 ≤ 2 / (q : ℝ) by positivity)
  have hdiag : (∑ n ∈ S, A n ^ 2) ≤ (24 / X) * X ^ (-2 * d) := by
    have he : (∑ n ∈ S, A n ^ 2) =
        ∑ n ∈ S, ‖GlobalZeroDensity.coefficient X n‖ ^ 2 *
          (n : ℝ) ^ (-(2 + 2 * d)) :=
      sum_congr rfl (fun n hn => rightTerm_square X d (hp n hn))
    rw [he]
    exact detector_right_diagonal hp hX1.le hd.le
  have hdiag' := mul_le_mul_of_nonneg_left hdiag (show 0 ≤ 2 * T by positivity)
  dsimp [A] at hm' hk hdiag'
  have hfinal : familyMean q S (rightTerm X (1 + d)) (fun n => -Real.log n) T ≤
      2 * T * ((24 / X) * X ^ (-2 * d)) +
      2 * ((2 / q) * (3 * (1 + 1 / (2 * d)) ^ 4 +
        (2 / d) * (1 + 1 / ((3 / 2) * d)) ^ 4)) +
      4 * ((2 / q) * X ^ (-d) * (1 + 1 / d) ^ 5) := by
    linarith only [hm', hk, hmass, hmass', hlog, hdiag']
  exact hfinal.trans_eq (by ring)

#print axioms family_right_finite_mean

end LiuWang.Proof.Campaign20260915.Density
