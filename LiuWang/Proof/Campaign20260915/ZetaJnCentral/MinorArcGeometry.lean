import LiuWang.Proof.Campaign20260915.ZetaJnCentral.PoleArcIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaJnCentral

open LiuWang.Proof.Campaign20260915.ZetaValidation

def sourcePoleNormal : ℂ := I * rsDescentDirection

theorem sourcePoleNormal_coordinates :
    sourcePoleNormal = (1 + I) / Real.sqrt 2 := by
  unfold sourcePoleNormal rsDescentDirection
  rw [mul_div, mul_sub, mul_one, I_mul_I]
  ring

theorem sourcePoleNormal_norm : ‖sourcePoleNormal‖ = 1 := by
  rw [sourcePoleNormal, norm_mul, norm_I, rsDescentDirection_norm, one_mul]

def sourceMinorPoint (k : ℤ) (e theta : ℝ) : ℂ :=
  k + ((e * sourcePoleRadius : ℝ) : ℂ) * sourcePoleNormal * exp (theta * I)

def sourceMinorVelocity (e theta : ℝ) : ℂ :=
  ((e * sourcePoleRadius : ℝ) : ℂ) * sourcePoleNormal * (I * exp (theta * I))

theorem sourceMinorPoint_deriv (k : ℤ) (e theta : ℝ) :
    HasDerivAt (sourceMinorPoint k e) (sourceMinorVelocity e theta) theta := by
  have h := ((((ofRealCLM.hasDerivAt (x := theta)).mul_const I).cexp).const_mul
    (((e * sourcePoleRadius : ℝ) : ℂ) * sourcePoleNormal)).const_add (k : ℂ)
  unfold sourceMinorPoint
  simpa [sourceMinorPoint, sourceMinorVelocity, mul_assoc, mul_comm, mul_left_comm] using h

theorem sourceMinorPoint_radius (k : ℤ) {e : ℝ} (he : |e| = 1) (theta : ℝ) :
    ‖sourceMinorPoint k e theta - k‖ = sourcePoleRadius := by
  simp [sourceMinorPoint, norm_real, Real.norm_eq_abs, he,
    abs_of_pos sourcePoleRadius_pos, sourcePoleNormal_norm, norm_exp_ofReal_mul_I]

theorem sourceMinorVelocity_norm {e : ℝ} (he : |e| = 1) (theta : ℝ) :
    ‖sourceMinorVelocity e theta‖ = sourcePoleRadius := by
  simp [sourceMinorVelocity, norm_real, Real.norm_eq_abs, he,
    abs_of_pos sourcePoleRadius_pos, sourcePoleNormal_norm, norm_exp_ofReal_mul_I]

def sourceMinorCosine (eta : ℝ) (k : ℤ) (e : ℝ) : ℝ :=
  e * (eta - k) / (Real.sqrt 2 * sourcePoleRadius)

def sourceMinorAngle (eta : ℝ) (k : ℤ) (e : ℝ) : ℝ :=
  Real.arccos (sourceMinorCosine eta k e)

def sourceMinorY (eta : ℝ) (k : ℤ) (e theta : ℝ) : ℝ :=
  -(eta - k) / Real.sqrt 2 - e * sourcePoleRadius * Real.sin theta

theorem sourceMinorCosine_mem {eta e : ℝ} {k : ℤ} (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    0 < sourceMinorCosine eta k e ∧ sourceMinorCosine eta k e ≤ 1 := by
  have hc : 0 < Real.sqrt 2 * sourcePoleRadius := by
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) sourcePoleRadius_pos
  unfold sourceMinorCosine
  refine ⟨div_pos hside hc, (div_le_one hc).mpr ?_⟩
  calc
    _ = |eta - k| := by
      rw [← abs_of_pos hside, abs_mul, he, one_mul]
    _ ≤ _ := hk

theorem sourceMinorAngle_mem {eta e : ℝ} {k : ℤ} (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) :
    0 ≤ sourceMinorAngle eta k e ∧ sourceMinorAngle eta k e < Real.pi / 2 := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_lt_pi_div_two.mpr
    (sourceMinorCosine_mem he hside hk).1⟩

theorem sourceMinorPoint_axis (k : ℤ) (e theta : ℝ) :
    (sourceMinorPoint k e theta).re + (sourceMinorPoint k e theta).im =
      k + Real.sqrt 2 * e * sourcePoleRadius * Real.cos theta := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp [sourceMinorPoint, sourcePoleNormal_coordinates, mul_re, mul_im, exp_re, exp_im]
  field_simp
  ring_nf
  rw [hs]
  ring

theorem sourceMinorPoint_side {eta e : ℝ} {k : ℤ} (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    {theta : ℝ} (ht : theta ∈ Icc (-sourceMinorAngle eta k e) (sourceMinorAngle eta k e)) :
    e * (k : ℝ) <
      e * ((sourceMinorPoint k e theta).re + (sourceMinorPoint k e theta).im) := by
  have ha := sourceMinorAngle_mem he hside hk
  have hc : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he2 : e ^ 2 = 1 := by nlinarith [sq_abs e]
  rw [sourceMinorPoint_axis]
  have hp : 0 < Real.sqrt 2 * sourcePoleRadius * Real.cos theta :=
    mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) sourcePoleRadius_pos) hc
  have hid : e * ((k : ℝ) + Real.sqrt 2 * e * sourcePoleRadius * Real.cos theta) =
      e * k + Real.sqrt 2 * sourcePoleRadius * Real.cos theta := by
    ring_nf
    rw [he2]
    ring
  rw [hid]
  linarith

theorem sourceMinorPoint_descent_decomposition (eta : ℝ) (k : ℤ) (e theta : ℝ) :
    sourceMinorPoint k e theta =
      rsDescentPoint eta (sourceMinorY eta k e theta) +
        sourcePoleNormal *
          ((e * sourcePoleRadius * Real.cos theta - (eta - k) / Real.sqrt 2 : ℝ) : ℂ) := by
  have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [sourceMinorPoint, sourceMinorY, sourcePoleNormal_coordinates,
      rsDescentPoint, rsDescentDirection, mul_re, mul_im, exp_re, exp_im]
    field_simp
    ring_nf
    rw [hs]
    simp only [sin_ofReal_re, cos_ofReal_re]
    ring
  · simp [sourceMinorPoint, sourceMinorY, sourcePoleNormal_coordinates,
      rsDescentPoint, rsDescentDirection, mul_re, mul_im, exp_re, exp_im]
    field_simp
    simp only [sin_ofReal_re, cos_ofReal_re]
    ring

theorem sourceMinorPoint_endpoint {eta e : ℝ} {k : ℤ} (he : |e| = 1)
    (hside : 0 < e * (eta - k)) (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius)
    {theta : ℝ} (ht : theta = sourceMinorAngle eta k e ∨ theta = -sourceMinorAngle eta k e) :
    sourceMinorPoint k e theta = rsDescentPoint eta (sourceMinorY eta k e theta) := by
  have hq := sourceMinorCosine_mem he hside hk
  have hc : Real.cos theta = sourceMinorCosine eta k e := by
    rcases ht with rfl | rfl
    · exact Real.cos_arccos (by linarith [hq.1]) hq.2
    · rw [Real.cos_neg]
      exact Real.cos_arccos (by linarith [hq.1]) hq.2
  have he2 : e ^ 2 = 1 := by nlinarith [sq_abs e]
  have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hr0 := sourcePoleRadius_pos.ne'
  have hz : e * sourcePoleRadius * Real.cos theta - (eta - k) / Real.sqrt 2 = 0 := by
    rw [hc, sourceMinorCosine]
    field_simp
    rw [he2]
    ring
  rw [sourceMinorPoint_descent_decomposition, hz, ofReal_zero, mul_zero, add_zero]

theorem sourceMinorPoint_distance {eta e : ℝ} {k : ℤ} (he : |e| = 1)
    (hk : |eta - k| ≤ Real.sqrt 2 * sourcePoleRadius) (theta : ℝ) :
    ‖sourceMinorPoint k e theta - eta‖ ≤ sourcePoleDistance := by
  calc
    _ = ‖(sourceMinorPoint k e theta - k) + ((k : ℂ) - eta)‖ := by
      congr 1
      ring
    _ ≤ ‖sourceMinorPoint k e theta - k‖ + ‖(k : ℂ) - eta‖ := norm_add_le _ _
    _ = sourcePoleRadius + |eta - k| := by
      rw [sourceMinorPoint_radius k he, ← ofReal_intCast, ← ofReal_sub, norm_real,
        Real.norm_eq_abs, abs_sub_comm]
    _ ≤ _ := by unfold sourcePoleDistance; linarith

end LiuWang.Proof.Campaign20260915.ZetaJnCentral
