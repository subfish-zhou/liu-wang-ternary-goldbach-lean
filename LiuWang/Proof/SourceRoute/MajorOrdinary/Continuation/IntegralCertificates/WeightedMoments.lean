import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.LogEnvelope
import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.SumIntegral

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

def momentPrimitive (r : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1 / r
  | n + 1, z => z ^ (n + 1) / r - (n + 1) / r * momentPrimitive r n z

theorem momentPrimitive_deriv {r : ℝ} (hr : r ≠ 0) (n : ℕ) (z : ℝ) :
    HasDerivAt (momentPrimitive r n) (z ^ n - r * momentPrimitive r n z) z := by
  induction n with
  | zero => simpa [momentPrimitive, hr] using hasDerivAt_const z (1 / r)
  | succ n ih =>
    convert! (((hasDerivAt_id z).pow (n + 1)).div_const r).sub
      (ih.const_mul ((n + 1) / r)) using 1
    dsimp [momentPrimitive]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring

def squarePrimitive (r a b c d z : ℝ) : ℝ :=
  a ^ 2 * momentPrimitive r 0 z +
    (2 * a * b) * momentPrimitive r 1 z +
    (b ^ 2 + 2 * a * c) * momentPrimitive r 2 z +
    (2 * a * d + 2 * b * c) * momentPrimitive r 3 z +
    (c ^ 2 + 2 * b * d) * momentPrimitive r 4 z +
    (2 * c * d) * momentPrimitive r 5 z +
    d ^ 2 * momentPrimitive r 6 z

theorem squarePrimitive_deriv {r : ℝ} (hr : r ≠ 0) (a b c d z : ℝ) :
    HasDerivAt (squarePrimitive r a b c d)
      ((a + b * z + c * z ^ 2 + d * z ^ 3) ^ 2 - r * squarePrimitive r a b c d z) z := by
  convert! ((((((momentPrimitive_deriv hr 0 z).const_mul (a ^ 2)).add
    ((momentPrimitive_deriv hr 1 z).const_mul (2 * a * b))).add
    ((momentPrimitive_deriv hr 2 z).const_mul (b ^ 2 + 2 * a * c))).add
    ((momentPrimitive_deriv hr 3 z).const_mul (2 * a * d + 2 * b * c))).add
    ((momentPrimitive_deriv hr 4 z).const_mul (c ^ 2 + 2 * b * d))).add
    ((momentPrimitive_deriv hr 5 z).const_mul (2 * c * d)) |>.add
    ((momentPrimitive_deriv hr 6 z).const_mul (d ^ 2)) using 1
  unfold squarePrimitive
  ring

def weightedSquarePrimitive (r t a b c d x : ℝ) : ℝ :=
  x ^ r * squarePrimitive r a b c d (Real.log x - t)

theorem weightedSquarePrimitive_deriv {r x : ℝ} (hr : r ≠ 0) (hx : 0 < x)
    (t a b c d : ℝ) :
    HasDerivAt (weightedSquarePrimitive r t a b c d)
      (x ^ (r - 1) * (a + b * (Real.log x - t) +
        c * (Real.log x - t) ^ 2 + d * (Real.log x - t) ^ 3) ^ 2) x := by
  convert! (Real.hasDerivAt_rpow_const (p := r) (Or.inl hx.ne')).mul
    ((squarePrimitive_deriv hr a b c d (Real.log x - t)).comp x
      ((Real.hasDerivAt_log hx.ne').sub_const t)) using 1
  dsimp
  rw [Real.rpow_sub hx, Real.rpow_one]
  field_simp
  ring

theorem weighted_square_integrable (r t a b c d : ℝ) {A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun x => x ^ (r - 1) *
      (a + b * (Real.log x - t) + c * (Real.log x - t) ^ 2 +
        d * (Real.log x - t) ^ 3) ^ 2) volume A B := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hAB]
  apply ContinuousOn.mul
  · exact continuousOn_id.rpow_const (fun x hx => Or.inl (by
      change x ≠ 0
      linarith [hx.1]))
  · have hl : ContinuousOn Real.log (Icc A B) :=
      Real.continuousOn_log.mono (fun x hx => ne_of_gt (hA.trans_le hx.1))
    exact ((((continuousOn_const.add (continuousOn_const.mul (hl.sub continuousOn_const))).add
      (continuousOn_const.mul ((hl.sub continuousOn_const).pow 2))).add
      (continuousOn_const.mul ((hl.sub continuousOn_const).pow 3))).pow 2)

theorem weighted_square_integral {r A B : ℝ} (hr : r ≠ 0) (hA : 0 < A) (hAB : A ≤ B)
    (t a b c d : ℝ) :
    (∫ x in A..B, x ^ (r - 1) *
      (a + b * (Real.log x - t) + c * (Real.log x - t) ^ 2 +
        d * (Real.log x - t) ^ 3) ^ 2) =
      weightedSquarePrimitive r t a b c d B - weightedSquarePrimitive r t a b c d A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · rw [uIcc_of_le hAB]
    exact fun x hx => weightedSquarePrimitive_deriv hr (hA.trans_le hx.1) t a b c d
  · exact weighted_square_integrable r t a b c d hA hAB

theorem kernel_integral_le_cubic {s A B t : ℝ} (hs : s - 1 ≠ 0)
    (hA : 100000 ≤ A) (hAB : A ≤ B) (ht : 11.5 ≤ t) :
    (∫ x in A..B, nuKernel s x) ≤
      weightedSquarePrimitive (s - 1) t (logNu t) (logNuD1 t) (logNuD2 t / 2) (logNuD3 t / 6) B -
      weightedSquarePrimitive (s - 1) t (logNu t) (logNuD1 t) (logNuD2 t / 2) (logNuD3 t / 6) A := by
  rw [← weighted_square_integral hs (by linarith) hAB]
  apply intervalIntegral.integral_mono_on hAB (nuKernel_intervalIntegrable s hA hAB)
    (weighted_square_integrable _ _ _ _ _ _ (by linarith) hAB)
  intro x hx
  have he : logNu t + logNuD1 t * (Real.log x - t) +
      (logNuD2 t / 2) * (Real.log x - t) ^ 2 +
      (logNuD3 t / 6) * (Real.log x - t) ^ 3 = cubic t (Real.log x) := by
    unfold cubic
    ring
  rw [he, show s - 1 - 1 = s - 2 by ring]
  exact mul_le_mul_of_nonneg_left (nu_sq_le_cubic_sq (hA.trans hx.1) ht)
    (Real.rpow_nonneg (by linarith [hx.1]) _)

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
