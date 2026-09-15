import LiuWang.Proof.SourceRoute.Density.Restart.ProductReflection
import LiuWang.Proof.SourceRoute.Density.Restart.FamilyMaximum
import LiuWang.Proof.SourceRoute.Density.ReflectedJensen

/-! Chen's Jensen step with one whole-family maximum and the original radii. -/

set_option autoImplicit false

noncomputable section

open Complex Set Metric
open scoped ComplexConjugate

namespace LiuWang.Proof.SourceRoute.Density.Restart

theorem productReflection_neg (q : ℕ) [NeZero q] (X U : ℝ) :
    productReflection q X (-U) = productReflection q X U := by
  funext s
  simp only [productReflection, ofReal_neg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]
  exact add_comm _ _

theorem productReflectedZeros_neg (q : ℕ) [NeZero q] (X U r : ℝ) :
    productReflectedZeros q X (-U) r = productReflectedZeros q X U r := by
  simp only [productReflectedZeros, productReflection_neg]

theorem productReflection_disk_bound (q : ℕ) [NeZero q] (X : ℝ) {T U R : ℝ}
    (hwin : |U - T| + R ≤ 3 / 2) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) R) :
    ‖productReflection q X U s‖ ≤ 2 * Real.exp (familyMaximum q X T (2 - R) (2 + R)) := by
  have hc : conj s ∈ closedBall (2 : ℂ) R := by
    rw [mem_closedBall_iff_norm]
    have he : conj s - 2 = conj (s - 2) := by simp only [map_sub, map_ofNat]
    rw [he, norm_conj]
    exact mem_closedBall_iff_norm.mp hs
  have hm : familySquare q X (s - U * I) = familySquare q X (conj s + U * I) := by
    have he : s - U * I = conj (conj s + U * I) := by simp [sub_eq_add_neg]
    rw [he, familySquare_conj]
  have hp := (norm_familyProduct_le_exp q X (s + U * I)).trans
    (Real.exp_le_exp.mpr (shifted_familySquare_le_maximum q X hwin hs))
  have hn := norm_familyProduct_le_exp q X (s - U * I)
  rw [hm] at hn
  have hn' := hn.trans (Real.exp_le_exp.mpr (shifted_familySquare_le_maximum q X hwin hc))
  exact (norm_add_le _ _).trans ((add_le_add hp hn').trans_eq (by ring))

theorem product_jensen_common_maximum (q : ℕ) [NeZero q] {X T U r R : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (hr : 0 < r) (hrR : r < R)
    (hwin : |U - T| + R ≤ 3 / 2) :
    ((productReflectedZeros q X U r).card : ℝ) ≤
      (Real.log (2 / (199499 / 100000 : ℝ)) + familyMaximum q X T (2 - R) (2 + R)) /
        Real.log (R / r) := by
  have hRp : 0 < R := hr.trans hrR
  have hE := familyMaximum_nonneg q X T (by linarith : 2 - R ≤ 2 + R)
  have hM : 1 ≤ 2 * Real.exp (familyMaximum q X T (2 - R) (2 + R)) := by
    have he := Real.add_one_le_exp (familyMaximum q X T (2 - R) (2 + R))
    linarith
  have hj := AnalyticOnNhd.sum_divisor_le (c := (2 : ℂ)) (f := productReflection q X U)
    (r := r) (R := R) (M := 2 * Real.exp (familyMaximum q X T (2 - R) (2 + R)))
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos hRp] using hrR)
    hM (fun s _ => (productReflection_differentiable q X U).analyticAt s)
    (productReflection_center_ne_zero q hX hqX U)
    (fun s hs => productReflection_disk_bound q X hwin
      (sphere_subset_closedBall (by simpa only [abs_of_pos hRp] using hs)))
  rw [abs_of_pos hr] at hj
  have hn := (productReflection_source_center q hX hqX U).trans
    (Complex.re_le_norm (productReflection q X U 2))
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  apply ((product_reflected_card_le_divisor q hX hqX U r).trans hj).trans
  apply div_le_div_of_nonneg_right _ hlog.le
  have he : Real.log (2 * Real.exp (familyMaximum q X T (2 - R) (2 + R)) /
      (199499 / 100000 : ℝ)) =
      Real.log (2 / (199499 / 100000 : ℝ)) + familyMaximum q X T (2 - R) (2 + R) := by
    rw [show 2 * Real.exp (familyMaximum q X T (2 - R) (2 + R)) / (199499 / 100000 : ℝ) =
      (2 / (199499 / 100000 : ℝ)) * Real.exp (familyMaximum q X T (2 - R) (2 + R)) by ring,
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  rw [← he]
  exact Real.log_le_log (div_pos (by positivity) (lt_of_lt_of_le (by norm_num) hn))
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) hn)

theorem product_source_radii_count (q : ℕ) [NeZero q] {X T U xi d : ℝ}
    (hX : 100000 ≤ X) (hqX : (q : ℝ) ≤ X) (hd : 0 < d)
    (hxi : 1 / 2 + 2 * d ≤ xi) (hxi1 : xi < 1)
    (hwin : |U - T| + (2 - xi + 3 * d / 2) ≤ 3 / 2) :
    ((productReflectedZeros q X U (2 - xi + d)).card : ℝ) ≤
      3 / d * (Real.log (2 / (199499 / 100000 : ℝ)) +
        familyMaximum q X T (xi - 3 * d / 2) (4 - xi + 3 * d / 2)) := by
  have hr : 0 < 2 - xi + d := by linarith
  have hrR : 2 - xi + d < 2 - xi + 3 * d / 2 := by linarith
  have hj := product_jensen_common_maximum q hX hqX hr hrR hwin
  have hlog := source_radii_log_lower hd hxi hxi1
  have he : 2 - (2 - xi + 3 * d / 2) = xi - 3 * d / 2 := by ring
  have he' : 2 + (2 - xi + 3 * d / 2) = 4 - xi + 3 * d / 2 := by ring
  rw [he, he'] at hj
  have hN : 0 ≤ Real.log (2 / (199499 / 100000 : ℝ)) +
      familyMaximum q X T (xi - 3 * d / 2) (4 - xi + 3 * d / 2) := by
    apply add_nonneg (Real.log_nonneg (by norm_num))
    exact familyMaximum_nonneg q X T (by linarith)
  exact hj.trans ((div_le_div_of_nonneg_left hN (by positivity : 0 < d / 3) hlog).trans_eq
    (by field_simp))

end LiuWang.Proof.SourceRoute.Density.Restart
