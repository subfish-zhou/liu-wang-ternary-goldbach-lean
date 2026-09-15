import LiuWang.Proof.SourceRoute.Density.Restart.SourceParameters
import LiuWang.Proof.SourceRoute.Density.Restart.WindowClosure

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate
open LiuWang.Proof.Interfaces (Character)
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem regression_empty_families (X : ℝ) (s : ℂ) :
    familyProduct 1 X s = 1 ∧ familyProduct 2 X s = 1 := by simp

theorem regression_inverse_full_family (chi : Character 8) (X : ℝ) (s : ℂ) :
    Q chi⁻¹ X (conj s) = conj (Q chi X s) ∧ familyProduct 8 X (conj s) = conj (familyProduct 8 X s) :=
  ⟨Q_inv_conj chi X s, familyProduct_conj 8 X s⟩

theorem regression_original_center (q : ℕ) [NeZero q] (hq : q ≤ 100000) (U : ℝ) :
    199499 / 100000 ≤ (productReflection q 100000 U 2).re :=
  productReflection_source_center q le_rfl (by exact_mod_cast hq) U

theorem regression_original_radii {d xi : ℝ} (hd : 0 < d)
    (hxi : 1 / 2 + 2 * d ≤ xi) (hxi1 : xi < 1) :
    d / 3 ≤ Real.log ((2 - xi + 3 * d / 2) / (2 - xi + d)) :=
  source_radii_log_lower hd hxi hxi1

theorem regression_no_sup_sum_exchange (q : ℕ) [NeZero q] (X T a b : ℝ) (hab : a ≤ b) :
    familyMaximum q X T a b =
      sSup ((fun sigma : ℝ => sSup ((fun t : ℝ => ∑ chi ∈ nonprincipalCharacters q,
        ‖f chi X ((sigma : ℂ) + t * I)‖ ^ 2) '' Ioo (T - 3 / 2) (T + 3 / 2))) '' Icc a b) := by
  rw [familyMaximum_eq_nested q X T hab]
  simp only [familyWindow_eq_open, familySquare]

theorem regression_phi_normalization (q : ℕ) [NeZero q] (X sigma U : ℝ) :
    familyMean q X sigma U = (q.totient : ℝ) * Fmean q X sigma U :=
  familyMean_eq_phi_Fmean q X sigma U

theorem regression_closed_count_nonempty :
    ∃ a ∈ Ioo (15 / 16 : ℝ) (47 / 50), ∃ U ∈ Ioo (100000 : ℝ) (100000 + 1 / 400),
      2 * Real.pi * (1 / 100) * (nonprincipalCount 3 (19 / 20) 100000 : ℝ) ≤
        familyMean 3 300000 a U + 3 / 2 * familyMean 3 300000 2 U +
          productHorizontalCost 3 300000 100000 a (1 / 100) := by
  have hlog : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  obtain ⟨a, ha, U, hU, _, h⟩ := source_qT_product_count 3 le_rfl
    (T := 100000) (alpha := 19 / 20) (d := 1 / 100) (e := 1 / 400)
    (by norm_num) (by norm_num; linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨a, ?_, U, hU, ?_⟩
  · norm_num at ha ⊢
    exact ha
  · norm_num at h ⊢
    exact h

end LiuWang.Proof.SourceRoute.Density.Restart
