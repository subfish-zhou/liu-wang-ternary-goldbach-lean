import LiuWang.Proof.SourceRoute.Density.Restart.ProductHorizontal
import LiuWang.Proof.SourceRoute.Density.Restart.ProductVertical

/-! Closed-height ordinary character multiplicities through the source whole-product route. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.NonprincipalDensityMeans (nonprincipalRatio)
open LiuWang.Proof.NonprincipalDensityMeans.Continuation.Frontier.Axis.PVContinuation

namespace LiuWang.Proof.SourceRoute.Density.Restart

def productHorizontalCost (q : ℕ) [NeZero q] (X T a d : ℝ) : ℝ :=
  2 * (2 - a) * Real.pi *
    (3 / d * (Real.log (2 / (199499 / 100000 : ℝ)) +
      familyMaximum q X T (a - 3 * d / 2) (4 - a + 3 * d / 2)) + 1)

theorem closed_count_product_source (q : ℕ) [NeZero q] {X alpha T a U d : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X)
    (hU : 0 ≤ U) (hTU : T ≤ U) (hd : 0 < d)
    (ha : 1 / 2 + 2 * d ≤ a) (ha1 : a < 1) (hgap : a + d ≤ alpha)
    (hwin : |U - T| + (2 - a + 3 * d / 2) ≤ 3 / 2)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) :
    2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
      familyMean q X a U + 3 / 2 * familyMean q X 2 U + productHorizontalCost q X T a d := by
  have hcount := closed_count_product_littlewood q (by linarith) (by linarith)
    hU hTU hd.le hgap hb
  have hh := product_horizontal_source_bound q hX hqX (by linarith) hU hd ha ha1
    (show a - d ≤ a by linarith) hwin
    (fun s hs => familyProduct_ne_zero (fun chi hc => hb chi hc s hs))
  exact hcount.trans (add_le_add (product_vertical_source q (by linarith) hU hb) hh)

theorem produced_product_count (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (halpha : alpha ≤ 1)
    (hleft : 1 / 2 + 2 * d ≤ alpha - d - e) (hT : 0 ≤ T)
    (hd : 0 < d) (he : 0 < e) (hed : e ≤ d / 2) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I), H chi X s ≠ 0) ∧
      2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
        familyMean q X a U + 3 / 2 * familyMean q X 2 U + productHorizontalCost q X T a d := by
  obtain ⟨a, ha, U, hU, hb⟩ :=
    family_boundary_perturbation q (by linarith : 3 < X) he (a := alpha - d) (T := T)
  refine ⟨a, ha, U, hU, hb, ?_⟩
  have haw : 1 / 2 + 2 * d ≤ a := hleft.trans ha.1.le
  have hwin : |U - T| + (2 - a + 3 * d / 2) ≤ 3 / 2 := by
    rw [abs_of_pos (sub_pos.mpr hU.1)]
    linarith only [haw, hU.2, hed]
  exact closed_count_product_source q hX hqX (by linarith [hU.1]) hU.1.le hd
    haw (by linarith [ha.2]) (by linarith [ha.2]) hwin hb

theorem produced_product_count_PV (q : ℕ) [NeZero q] {X alpha T d e : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (halpha : alpha ≤ 1)
    (hleft : 1 / 2 + 2 * d ≤ alpha - d - e) (hT : 0 ≤ T)
    (hd : 0 < d) (he : 0 < e) (hed : e ≤ d / 2) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
        (q.totient : ℝ) * pvBudget q X ⌈X⌉₊ a U +
          12 * U * (q.totient - 1 : ℕ) / (X - 1) ^ 2 + productHorizontalCost q X T a d := by
  obtain ⟨a, ha, U, hU, _, h⟩ := produced_product_count q hX hqX halpha hleft hT hd he hed
  have hUp : 0 ≤ U := by linarith [hU.1]
  have hqN : q ≤ ⌈X⌉₊ := by exact_mod_cast hqX.trans (Nat.le_ceil X)
  have hm : familyMean q X a U ≤ (q.totient : ℝ) * pvBudget q X ⌈X⌉₊ a U := by
    rw [familyMean_eq_phi_Fmean]
    exact mul_le_mul_of_nonneg_left
      (Fmean_PV_mother q X (by linarith) le_rfl hqN
        ⟨by linarith [ha.1], by linarith [ha.2]⟩ hUp) (Nat.cast_nonneg _)
  have hr : 3 / 2 * familyMean q X 2 U ≤
      12 * U * (q.totient - 1 : ℕ) / (X - 1) ^ 2 :=
    (mul_le_mul_of_nonneg_left (familyMean_two_le q (by linarith) hUp)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans_eq (by ring)
  exact ⟨a, ha, U, hU, h.trans (add_le_add (add_le_add hm hr) le_rfl)⟩

theorem source_qT_product_count (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {alpha T d e : ℝ} (hXT : 100000 ≤ (q : ℝ) * T)
    (hT : 10000 * Real.log q ≤ T) (halpha : alpha ≤ 1)
    (hleft : 1 / 2 + 2 * d ≤ alpha - d - e)
    (hd : 0 < d) (he : 0 < e) (hed : e ≤ d / 2) :
    ∃ a ∈ Ioo (alpha - d - e) (alpha - d), ∃ U ∈ Ioo T (T + e),
      (∀ chi ∈ nonprincipalCharacters q,
        ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
          H chi ((q : ℝ) * T) s ≠ 0) ∧
      2 * Real.pi * d * (nonprincipalCount q alpha T : ℝ) ≤
        familyMean q ((q : ℝ) * T) a U + 3 / 2 * familyMean q ((q : ℝ) * T) 2 U +
          productHorizontalCost q ((q : ℝ) * T) T a d :=
  produced_product_count q hXT (source_q_le_cutoff hq hT) halpha hleft
    (le_trans (by norm_num) (source_height_ge_one hq hT)) hd he hed

end LiuWang.Proof.SourceRoute.Density.Restart
