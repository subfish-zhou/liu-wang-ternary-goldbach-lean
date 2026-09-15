import LiuWang.Proof.Campaign20260915.ZetaWinding.TrapezoidRemainder

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Finset

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

def reciprocalProfile (a y u : ℝ) : ℝ := (a + u) / ((a + u) ^ 2 + y ^ 2)
def reciprocalSlope (a y u : ℝ) : ℝ := (y ^ 2 - (a + u) ^ 2) / ((a + u) ^ 2 + y ^ 2) ^ 2
def reciprocalCurvature (a y u : ℝ) : ℝ :=
  2 * (a + u) * ((a + u) ^ 2 - 3 * y ^ 2) / ((a + u) ^ 2 + y ^ 2) ^ 3
def reciprocalEnvelope (a y u : ℝ) : ℝ := 6 * (a + u) / ((a + u) ^ 2 + y ^ 2) ^ 2
def reciprocalPrimitive (a y u : ℝ) : ℝ := Real.log ((a + u) ^ 2 + y ^ 2) / 2
def reciprocalEnvelopePrimitive (a y u : ℝ) : ℝ := -3 / ((a + u) ^ 2 + y ^ 2)

theorem reciprocalProfile_derivatives {a y u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    HasDerivAt (reciprocalProfile a y) (reciprocalSlope a y u) u ∧
    HasDerivAt (reciprocalSlope a y) (reciprocalCurvature a y u) u := by
  have hd : HasDerivAt (fun x : ℝ => a + x) 1 u := by simpa using (hasDerivAt_id u).const_add a
  have hden := (hd.pow 2).add_const (y ^ 2)
  have hn : (a + u) ^ 2 + y ^ 2 ≠ 0 := by positivity
  constructor
  · convert! hd.div hden hn using 1
    dsimp [reciprocalSlope]
    field_simp
    ring
  · have hh := ((hd.pow 2).const_sub (y ^ 2)).div (hden.pow 2) (pow_ne_zero 2 hn)
    convert! hh using 1
    dsimp [reciprocalCurvature]
    field_simp
    ring

theorem reciprocalPrimitive_derivatives {a y u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    HasDerivAt (reciprocalPrimitive a y) (reciprocalProfile a y u) u ∧
    HasDerivAt (reciprocalEnvelopePrimitive a y) (reciprocalEnvelope a y u) u := by
  have hd : HasDerivAt (fun x : ℝ => a + x) 1 u := by simpa using (hasDerivAt_id u).const_add a
  have hden := (hd.pow 2).add_const (y ^ 2)
  have hn : (a + u) ^ 2 + y ^ 2 ≠ 0 := by positivity
  constructor
  · convert! (hden.log hn).div_const 2 using 1
    dsimp [reciprocalProfile]
    ring
  · convert! (hasDerivAt_const u (-3 : ℝ)).div hden hn using 1
    dsimp [reciprocalEnvelope]
    ring

theorem reciprocalCurvature_bound {a y u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    |reciprocalCurvature a y u| ≤ reciprocalEnvelope a y u := by
  have hr : 0 < a + u := by linarith
  have hn : 0 < (a + u) ^ 2 + y ^ 2 := by positivity
  have hb : |(a + u) ^ 2 - 3 * y ^ 2| ≤ 3 * ((a + u) ^ 2 + y ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (a + u), sq_nonneg y]
  dsimp [reciprocalCurvature, reciprocalEnvelope]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos hr, abs_of_pos (pow_pos hn 3)]
  apply (div_le_div_iff₀ (pow_pos hn 3) (pow_pos hn 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (a + u) * ((a + u)^2 + y^2)^2 by positivity)]

theorem reciprocal_quadrature_bound {a : ℝ} (ha : 0 < a) (y : ℝ) (N : ℕ) :
    |(∑ n ∈ range N, reciprocalProfile a y n) +
        (reciprocalProfile a y N - reciprocalProfile a y 0) / 2 -
        (reciprocalPrimitive a y N - reciprocalPrimitive a y 0)| ≤
      3 / (8 * (a ^ 2 + y ^ 2)) := by
  have hh : ContinuousOn (reciprocalCurvature a y) (Set.Ici 0) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hu' : 0 ≤ u := hu
    positivity
  have hc : ContinuousOn (reciprocalEnvelope a y) (Set.Ici 0) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hu' : 0 ≤ u := hu
    positivity
  have h := trapezoid_sum_abs
    (fun u hu => (reciprocalProfile_derivatives ha hu).1)
    (fun u hu => (reciprocalProfile_derivatives ha hu).2) hh hc
    (fun u hu => reciprocalCurvature_bound ha hu)
    (fun u hu => (reciprocalPrimitive_derivatives ha hu).1)
    (fun u hu => (reciprocalPrimitive_derivatives ha hu).2) N
  refine h.trans ?_
  simp only [reciprocalEnvelopePrimitive, add_zero]
  have hn : 0 ≤ 3 / ((a + N) ^ 2 + y ^ 2) := by positivity
  rw [neg_div, neg_div]
  rw [show 3 / (8 * (a^2 + y^2)) = (3 / (a^2 + y^2)) / 8 by
    rw [mul_comm (8 : ℝ), div_mul_eq_div_div]]
  linarith

#print axioms reciprocalProfile_derivatives
#print axioms reciprocalCurvature_bound
#print axioms reciprocal_quadrature_bound

end LiuWang.Proof.Campaign20260915.ZetaWinding
