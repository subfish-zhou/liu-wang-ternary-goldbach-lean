import LiuWang.Proof.Campaign20260915.Density.HorizontalPayment
import LiuWang.Proof.Campaign20260915.Density.NearMean
import LiuWang.Proof.Campaign20260915.Density.ChenLow

set_option autoImplicit false
noncomputable section

open Complex Set
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.SourceRoute.Density
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

theorem source_count_at_regular_boundary (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y alpha a U : ℝ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ a)
    (hgap : a + sourceDelta ((q : ℝ) * y) ≤ alpha) (halpha : alpha ≤ 1)
    (hTU : y ≤ U) (hUy : |U - y| ≤ sourceDelta ((q : ℝ) * y) / 2)
    (hb : ∀ chi ∈ nonprincipalCharacters q,
      ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
        H chi ((q : ℝ) * y) s ≠ 0) :
    (nonprincipalCount q alpha y : ℝ) ≤
      chenBound q (a + sourceDelta ((q : ℝ) * y)) y := by
  let X : ℝ := (q : ℝ) * y
  let d : ℝ := sourceDelta X
  have hy' := source_height_ge_ten_thousand hy
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX : 100000 ≤ X := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    dsimp [X]
    nlinarith only [h]
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hd1 : d ≤ 1 / 12 := (source_product_shift_bounds q hy).2
  have hU : 0 ≤ U := by linarith
  have ha2 : a ≤ 2 := by change a + d ≤ alpha at hgap; linarith
  have hUy' : U ≤ y + 3 / 2 := by
    have h := (abs_le.mp hUy).2
    change U - y ≤ d / 2 at h
    linarith
  have hc := closed_count_product_littlewood q (by linarith : 3 < X)
    ha2 hU hTU hd.le hgap hb
  have hv := product_vertical_source q (by linarith : 5 ≤ X) hU hb
  have hh := source_product_horizontal_paid q hq hy ha (hgap.trans halpha) hU hUy
    (fun s hs => familyProduct_ne_zero (fun chi hchi => hb chi hchi s hs))
  have hm := source_vertical_enlarged q hy
    (alpha := a + d) (by change 1 / 2 + d ≤ a at ha; linarith)
    (hgap.trans halpha) hU hUy'
  rw [show a + d - d = a by ring] at hm
  have hden : 0 < 2 * Real.pi * d := by positivity
  have hc' : (nonprincipalCount q alpha y : ℝ) ≤
      ((familyMean q X a U + 3 / 2 * familyMean q X 2 U) +
        productHorizontal q X a U) / (2 * Real.pi * d) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hc, hv]
  rw [add_div] at hc'
  have he : chenBound q (a + d) y =
      (5700 + 250359 / Real.log X) * chenDensityScale q y (a + d) := by
    unfold chenBound chenDensityScale
    dsimp [X]
    ring
  change _ ≤ chenBound q (a + d) y
  rw [he]
  nlinarith only [hc', hm, hh]

theorem closed_nonprincipal_chen_high (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + 2 * sourceDelta ((q : ℝ) * y) < alpha) (ha1 : alpha < 1) :
    (nonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y := by
  let X : ℝ := (q : ℝ) * y
  let d : ℝ := sourceDelta X
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hy' := source_height_ge_ten_thousand hy
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hX : 3 < X := by dsimp [X]; nlinarith
  apply le_of_forall_pos_le_add
  intro eps heps
  have hcont : ContinuousAt (fun beta : ℝ => chenBound q beta y) alpha :=
    (continuous_chenBound q (by linarith : 1 < y)).continuousAt
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp hcont eps heps
  let e : ℝ := min r (min (d / 2) ((alpha - 1 / 2 - 2 * d) / 2))
  have he : 0 < e := by
    apply lt_min hr
    apply lt_min (by positivity)
    change 1 / 2 + 2 * d < alpha at ha
    linarith
  have her : e ≤ r := min_le_left _ _
  have hed : e ≤ d / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e ≤ (alpha - 1 / 2 - 2 * d) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨a, hab, U, hU, hb⟩ := family_boundary_perturbation q hX he (a := alpha - d) (T := y)
  have hal : 1 / 2 + d ≤ a := by
    change 1 / 2 + 2 * d < alpha at ha
    linarith [hab.1]
  have hgap : a + d ≤ alpha := by linarith [hab.2]
  have hUy : |U - y| ≤ d / 2 := by
    rw [abs_of_pos (by linarith [hU.1])]
    linarith [hU.2]
  have hc := source_count_at_regular_boundary q hq hy hal hgap ha1.le hU.1.le hUy hb
  have hdist : dist (a + d) alpha < r := by
    rw [Real.dist_eq, abs_of_neg (by linarith [hab.2] : a + d - alpha < 0)]
    linarith [hab.1]
  have hval := hnear hdist
  rw [Real.dist_eq] at hval
  exact hc.trans (by linarith [(abs_lt.mp hval).2])

theorem closed_nonprincipal_chen (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    (nonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y := by
  by_cases hlo : alpha ≤ 1 / 2 + 2 * sourceDelta ((q : ℝ) * y)
  · exact closed_nonprincipal_chen_low q hy ha
      (by linarith [(source_product_shift_bounds q hy).2])
  · exact closed_nonprincipal_chen_high q hq hy (lt_of_not_ge hlo) ha1

theorem strict_nonprincipal_chen (q : ℕ) [NeZero q] (hq : 3 ≤ q) {y alpha : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    (strictNonprincipalCount q alpha y : ℝ) ≤ chenBound q alpha y :=
  (Nat.cast_le.mpr (strict_nonprincipal_le_closed q alpha y)).trans
    (closed_nonprincipal_chen q hq hy ha ha1)

end LiuWang.Proof.Campaign20260915.Density
