import LiuWang.Proof.SourceRoute.Density.Restart.ProductCount

/-! The original delta and height domain automatically meet the high-real-part geometry. -/

set_option autoImplicit false

noncomputable section

open Complex Set
open LiuWang.Proof.NonprincipalDensityAdvance

namespace LiuWang.Proof.SourceRoute.Density.Restart

def sourceDelta (X : ℝ) : ℝ := 1 / ((3 / 2) * Real.log X)

theorem source_log_lower {X : ℝ} (hX : 100000 ≤ X) : 5 ≤ Real.log X := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hp : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 1024) (show (1024 : ℝ) ≤ X by linarith)
  rw [hp] at hm
  linarith

theorem sourceDelta_pos {X : ℝ} (hX : 100000 ≤ X) : 0 < sourceDelta X := by
  have hl := source_log_lower hX
  unfold sourceDelta
  positivity

theorem sourceDelta_le {X : ℝ} (hX : 100000 ≤ X) : sourceDelta X ≤ 2 / 15 := by
  have hl := source_log_lower hX
  unfold sourceDelta
  apply (div_le_iff₀ (by positivity : 0 < (3 / 2) * Real.log X)).mpr
  linarith

theorem source_high_geometry {X alpha : ℝ} (hX : 100000 ≤ X) (ha : 19 / 20 ≤ alpha) :
    1 / 2 + 2 * sourceDelta X ≤ alpha - sourceDelta X - sourceDelta X / 4 := by
  have hd := sourceDelta_le hX
  linarith

theorem source_high_count (q : ℕ) [NeZero q] (hq : 3 ≤ q) {alpha T : ℝ}
    (hT : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ T)
    (halpha : alpha ∈ Icc (19 / 20) 1) :
    ∃ a ∈ Ioo (alpha - sourceDelta ((q : ℝ) * T) - sourceDelta ((q : ℝ) * T) / 4)
        (alpha - sourceDelta ((q : ℝ) * T)),
      ∃ U ∈ Ioo T (T + sourceDelta ((q : ℝ) * T) / 4),
        (∀ chi ∈ nonprincipalCharacters q,
          ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
            H chi ((q : ℝ) * T) s ≠ 0) ∧
        2 * Real.pi * sourceDelta ((q : ℝ) * T) * (nonprincipalCount q alpha T : ℝ) ≤
          familyMean q ((q : ℝ) * T) a U + 3 / 2 * familyMean q ((q : ℝ) * T) 2 U +
            productHorizontalCost q ((q : ℝ) * T) T a (sourceDelta ((q : ℝ) * T)) := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hXT : 100000 ≤ (q : ℝ) * T := by
    have h := (div_le_iff₀ hqpos).mp ((le_max_left _ _).trans hT)
    simpa only [mul_comm] using h
  have hd := sourceDelta_pos hXT
  exact source_qT_product_count q hq hXT ((le_max_right _ _).trans hT) halpha.2
    (source_high_geometry hXT halpha.1) hd (by positivity) (by linarith)

end LiuWang.Proof.SourceRoute.Density.Restart
