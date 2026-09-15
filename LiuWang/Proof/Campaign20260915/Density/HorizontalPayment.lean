import LiuWang.Proof.Campaign20260915.Density.EnvelopeIntegral
import LiuWang.Proof.Campaign20260915.Density.MovingJensen

set_option autoImplicit false
noncomputable section

open Complex Set MeasureTheory
open LiuWang.Proof.SourceRoute.Density.Restart
open LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Continuation
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.Campaign20260915.Density

def horizontalArgumentMajorant (q : ℕ) (y x : ℝ) : ℝ :=
  (3 / sourceDelta ((q : ℝ) * y) * (Real.log (2 / (199499 / 100000 : ℝ)) +
    horizontalEnvelope q y (x - sourceDelta ((q : ℝ) * y) / 2)) + 1) * Real.pi

theorem horizontalArgumentMajorant_continuous (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    Continuous (horizontalArgumentMajorant q y) := by
  unfold horizontalArgumentMajorant
  exact ((continuous_const.mul (continuous_const.add
    ((horizontalEnvelope_continuous q hy).comp
      (continuous_id.sub continuous_const)))).add continuous_const).mul continuous_const

theorem source_horizontal_argument_moving (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y a U h x : ℝ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ a) (hU : 0 ≤ U)
    (hUy : |U - y| ≤ sourceDelta ((q : ℝ) * y) / 2)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q ((q : ℝ) * y) s ≠ 0)
    (hh : h = -U ∨ h = U) (hx : x ∈ Ioo a 2) :
    |(horizontalLog (familyProduct q ((q : ℝ) * y)) 2 U h x).im| ≤
      horizontalArgumentMajorant q y x := by
  let X : ℝ := (q : ℝ) * y
  let d : ℝ := sourceDelta X
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hy' := source_height_ge_ten_thousand hy
  have hX : 100000 ≤ X := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    dsimp [X]
    nlinarith only [h]
  have hqX : (q : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have hwin : |U - y| + (2 - x + d / 2) ≤ 3 / 2 := by
    change 1 / 2 + d ≤ a at ha
    change |U - y| ≤ d / 2 at hUy
    linarith [hx.1]
  have harg := product_horizontal_argument_moving q hX hqX hU hb hh
    ⟨hx.1.le, hx.2.le⟩ (le_refl (2 - x))
  have he : productReflectedZeros q X h (2 - x) = productReflectedZeros q X U (2 - x) := by
    rcases hh with rfl | rfl
    · exact productReflectedZeros_neg q X U (2 - x)
    · rfl
  rw [he] at harg
  have hc := product_moving_radii_count q hX hqX hd hx.2 hwin
  have hm := source_familyMaximum_envelope q hq hy
    (a := x - d / 2) (b := 4 - x + d / 2)
    (by change 1 / 2 + d ≤ a at ha; linarith [hx.1])
    (by linarith [hx.2]) (by linarith [hx.2])
  have hm' := mul_le_mul_of_nonneg_left
    (show Real.log (2 / (199499 / 100000 : ℝ)) +
        familyMaximum q X y (x - d / 2) (4 - x + d / 2) ≤
      Real.log (2 / (199499 / 100000 : ℝ)) + horizontalEnvelope q y (x - d / 2) by
        linarith only [hm])
    (show 0 ≤ 3 / d by positivity)
  have hc' : ((productReflectedZeros q X U (2 - x)).card + 1 : ℝ) ≤
      3 / d * (Real.log (2 / (199499 / 100000 : ℝ)) +
        horizontalEnvelope q y (x - d / 2)) + 1 := by linarith only [hc, hm']
  exact harg.trans (mul_le_mul_of_nonneg_right hc' Real.pi_pos.le)

theorem source_horizontal_integral_moving (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y a U h : ℝ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ a) (ha2 : a ≤ 2) (hU : 0 ≤ U)
    (hUy : |U - y| ≤ sourceDelta ((q : ℝ) * y) / 2)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q ((q : ℝ) * y) s ≠ 0)
    (hh : h = -U ∨ h = U) :
    |∫ x in a..2, (horizontalLog (familyProduct q ((q : ℝ) * y)) 2 U h x).im| ≤
      ∫ x in a..2, horizontalArgumentMajorant q y x := by
  have hd := entire_horizontalLog_data (familyProduct_differentiable q ((q : ℝ) * y)) hb hh
  have hf : IntervalIntegrable
      (fun x : ℝ => (horizontalLog (familyProduct q ((q : ℝ) * y)) 2 U h x).im) volume a 2 :=
    (Complex.continuous_im.comp_continuousOn hd.1).intervalIntegrable
  have hg : IntervalIntegrable (horizontalArgumentMajorant q y) volume a 2 :=
    (horizontalArgumentMajorant_continuous q hy).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo ha2 hf.norm hg (fun x hx => by
    simpa only [Real.norm_eq_abs] using source_horizontal_argument_moving q hq hy ha hU hUy hb hh hx)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun x : ℝ => (horizontalLog (familyProduct q ((q : ℝ) * y)) 2 U h x).im)
    (μ := volume) ha2
  simpa only [Real.norm_eq_abs] using hnorm.trans hm

theorem source_horizontal_majorant_integral (q : ℕ) [NeZero q] {y a : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (∫ x in a..2, horizontalArgumentMajorant q y x) =
      (3 / sourceDelta ((q : ℝ) * y) *
        (Real.log (2 / (199499 / 100000 : ℝ)) * (2 - a) +
          ∫ x in a..2, horizontalEnvelope q y (x - sourceDelta ((q : ℝ) * y) / 2)) +
        (2 - a)) * Real.pi := by
  have hi : IntervalIntegrable (fun x : ℝ =>
      horizontalEnvelope q y (x - sourceDelta ((q : ℝ) * y) / 2)) volume a 2 :=
    ((horizontalEnvelope_continuous q hy).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  unfold horizontalArgumentMajorant
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add ((intervalIntegrable_const.add hi).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem source_product_horizontal_paid (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {y a U : ℝ} (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y)
    (ha : 1 / 2 + sourceDelta ((q : ℝ) * y) ≤ a)
    (ha1 : a + sourceDelta ((q : ℝ) * y) ≤ 1) (hU : 0 ≤ U)
    (hUy : |U - y| ≤ sourceDelta ((q : ℝ) * y) / 2)
    (hb : ∀ s ∈ RectangleBorder ((a : ℂ) - U * I) ((2 : ℂ) + U * I),
      familyProduct q ((q : ℝ) * y) s ≠ 0) :
    productHorizontal q ((q : ℝ) * y) a U /
      (2 * Real.pi * sourceDelta ((q : ℝ) * y)) ≤
        250359 / Real.log ((q : ℝ) * y) *
          chenDensityScale q y (a + sourceDelta ((q : ℝ) * y)) := by
  let L : ℝ := Real.log ((q : ℝ) * y)
  let d : ℝ := sourceDelta ((q : ℝ) * y)
  let S : ℝ := chenDensityScale q y (a + d)
  let J : ℝ := ∫ x in a..2, horizontalEnvelope q y (x - d / 2)
  let C : ℝ := Real.log (2 / (199499 / 100000 : ℝ))
  have hL : 11 ≤ L := source_product_log_ge_eleven q hy
  have hL0 : 0 < L := by linarith
  have hd : 0 < d := (source_product_shift_bounds q hy).1
  have ha2 : a ≤ 2 := by change a + d ≤ 1 at ha1; linarith
  have hp := source_horizontal_integral_moving q hq hy ha ha2 hU hUy hb (Or.inr rfl)
  have hn := source_horizontal_integral_moving q hq hy ha ha2 hU hUy hb (Or.inl rfl)
  have hprod : productHorizontal q ((q : ℝ) * y) a U ≤
      2 * ((3 / d * (C * (2 - a) + J) + (2 - a)) * Real.pi) := by
    rw [source_horizontal_majorant_integral q hy] at hp hn
    unfold productHorizontal
    dsimp only [C, J, d]
    nlinarith only [(abs_le.mp hp).2, (abs_le.mp hn).1]
  have he : (2 * ((3 / d * (C * (2 - a) + J) + (2 - a)) * Real.pi)) /
      (2 * Real.pi * d) = 6.75 * L ^ 2 * (C * (2 - a) + J) + 1.5 * L * (2 - a) := by
    dsimp only [d, sourceDelta]
    change _ / (2 * Real.pi * (1 / (1.5 * L))) = _
    field_simp
    ring
  apply ((div_le_div_of_nonneg_right hprod (by positivity)).trans_eq he).trans
  have hC : C ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 / (199499 / 100000))
    dsimp [C]
    linarith
  have hlen : 0 ≤ 2 - a ∧ 2 - a ≤ 1.5 := by
    change 1 / 2 + d ≤ a at ha
    constructor <;> linarith
  have hcost := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right hC hlen.1).trans (by simpa using hlen.2))
    (show 0 ≤ 6.75 * L ^ 2 by positivity)
  have hcost' := mul_le_mul_of_nonneg_left hlen.2 (show 0 ≤ 1.5 * L by positivity)
  have hi := mul_le_mul_of_nonneg_left (source_horizontalEnvelope_integral q hy ha2 ha1)
    (show 0 ≤ 6.75 * L ^ 2 by positivity)
  have hie : 6.75 * L ^ 2 * (3000 * S / L ^ 3) = 20250 * S / L := by field_simp; ring
  change 6.75 * L ^ 2 * J ≤ 6.75 * L ^ 2 * (3000 * S / L ^ 3) at hi
  rw [hie] at hi
  have hs := source_density_scale_ge_log_six q hy ha1
  have hp3 : L ^ (3 : ℕ) ≤ L ^ (6 : ℕ) :=
    pow_le_pow_right₀ (by linarith : 1 ≤ L) (by decide : 3 ≤ 6)
  have hLS : L ^ 2 ≤ S / L := by
    apply (le_div_iff₀ hL0).mpr
    change L ^ 6 ≤ S at hs
    nlinarith only [hp3, hs]
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hSP : 0 ≤ S / L := div_nonneg (source_density_scale_pos q hy _).le hL0.le
  change _ ≤ 250359 / L * S
  simp only [div_eq_mul_inv] at hi hLS hSP ⊢
  nlinarith only [hcost, hcost', hi, hLS, hLL, hSP]

end LiuWang.Proof.Campaign20260915.Density
