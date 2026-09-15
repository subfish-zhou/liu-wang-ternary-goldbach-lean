import LiuWang.Proof.MajorZeroMomentPayment.RealMoments

/-! A joint eight-corner bound keeps all signs in the full simplex density.
Only the explicitly bounded finite-radius error is paid by norms. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.MajorZeroMomentPayment

def edgeLower (v u a b : ℝ) : ℝ := min (a*v+b) (a*u+b)

theorem affine_lower {v u x L a b : ℝ} (hx : v ≤ x ∧ x ≤ u)
    (hv : L ≤ a*v+b) (hu : L ≤ a*u+b) : L ≤ a*x+b := by
  by_cases ha : 0 ≤ a
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1)]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) (sub_nonpos.mpr hx.2)]

theorem edgeLower_le {v u x : ℝ} (hx : v ≤ x ∧ x ≤ u) (a b : ℝ) :
    edgeLower v u a b ≤ a*x+b :=
  affine_lower hx (min_le_left _ _) (min_le_right _ _)

def boxLower (v u D A B C : ℝ) : ℝ :=
  min
    (min (edgeLower v u (A+v*(B+v*C)) D) (edgeLower v u (A+u*(B+v*C)) D))
    (min (edgeLower v u (A+v*(B+u*C)) D) (edgeLower v u (A+u*(B+u*C)) D))

theorem boxLower_le {v u x y z : ℝ}
    (hx : v ≤ x ∧ x ≤ u) (hy : v ≤ y ∧ y ≤ u) (hz : v ≤ z ∧ z ≤ u)
    (D A B C : ℝ) :
    boxLower v u D A B C ≤ D + z*(A+y*(B+x*C)) := by
  have hll : boxLower v u D A B C ≤ (A+v*(B+v*C))*z+D :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans
    (edgeLower_le hz (A+v*(B+v*C)) D)
  have hlu : boxLower v u D A B C ≤ (A+u*(B+v*C))*z+D :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans
    (edgeLower_le hz (A+u*(B+v*C)) D)
  have hul : boxLower v u D A B C ≤ (A+v*(B+u*C))*z+D :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans
    (edgeLower_le hz (A+v*(B+u*C)) D)
  have huu : boxLower v u D A B C ≤ (A+u*(B+u*C))*z+D :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans
    (edgeLower_le hz (A+u*(B+u*C)) D)
  have hv : boxLower v u D A B C ≤ D+z*(A+y*(B+v*C)) := by
    have h := affine_lower hy (a := z*(B+v*C)) (b := D+z*A)
      (L := boxLower v u D A B C)
      (by nlinarith [hll]) (by nlinarith [hlu])
    nlinarith
  have hu : boxLower v u D A B C ≤ D+z*(A+y*(B+u*C)) := by
    have h := affine_lower hy (a := z*(B+u*C)) (b := D+z*A)
      (L := boxLower v u D A B C)
      (by nlinarith [hul]) (by nlinarith [huu])
    nlinarith
  have h := affine_lower hx (a := z*y*C) (b := D+z*A+z*y*B)
    (L := boxLower v u D A B C) (by nlinarith [hv]) (by nlinarith [hu])
  nlinarith

def jointFinite (N : ℕ) (delta beta : ℝ) (D A B C : ℂ) : ℂ :=
  D * finiteMoment N delta 1 1 1 +
    A * finiteMoment N delta 1 1 beta +
    B * finiteMoment N delta 1 beta beta +
    C * finiteMoment N delta beta beta beta

def jointFull (N : ℕ) (beta : ℝ) (D A B C : ℂ) : ℂ :=
  D * fullMoment N 1 1 1 +
    A * fullMoment N 1 1 beta +
    B * fullMoment N 1 beta beta +
    C * fullMoment N beta beta beta

def jointTail (N : ℕ) (delta beta : ℝ) (D A B C : ℂ) : ℝ :=
  (‖D‖ + ‖A‖*realEndpoint N beta + ‖B‖*realEndpoint N beta^2 +
    ‖C‖*realEndpoint N beta^3) / (Real.pi^3 * delta^2)

theorem jointFinite_eq_integral {N : ℕ} (hN : 0 < N) (delta beta : ℝ)
    (D A B C : ℂ) :
    jointFinite N delta beta D A B C =
      ∫ eta in -delta..delta,
        D*tripleKernel N 1 1 1 eta + A*tripleKernel N 1 1 beta eta +
          B*tripleKernel N 1 beta beta eta + C*tripleKernel N beta beta beta eta := by
  have hi0 := ((continuous_tripleKernel hN 1 1 1).const_mul D).intervalIntegrable
    (μ := volume) (-delta) delta
  have hi1 := ((continuous_tripleKernel hN 1 1 beta).const_mul A).intervalIntegrable
    (μ := volume) (-delta) delta
  have hi2 := ((continuous_tripleKernel hN 1 beta beta).const_mul B).intervalIntegrable
    (μ := volume) (-delta) delta
  have hi3 := ((continuous_tripleKernel hN beta beta beta).const_mul C).intervalIntegrable
    (μ := volume) (-delta) delta
  have he0 := intervalIntegral.integral_add hi0 hi1
  have he1 := intervalIntegral.integral_add (hi0.add hi1) hi2
  have he2 := intervalIntegral.integral_add ((hi0.add hi1).add hi2) hi3
  rw [he2, he1, he0]
  simp only [jointFinite, finiteMoment, intervalIntegral.integral_const_mul]

theorem joint_tail_bound {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : beta ≤ 1) (hd : 0 < delta) (D A B C : ℂ) :
    ‖jointFull N beta D A B C - jointFinite N delta beta D A B C‖ ≤
      jointTail N delta beta D A B C := by
  have h0 := moment_tail_real hN (r := 1) (s := 1) (t := 1) le_rfl le_rfl le_rfl hd
  have h1 := moment_tail_real hN (r := 1) (s := 1) (t := beta) le_rfl le_rfl hb hd
  have h2 := moment_tail_real hN (r := 1) (s := beta) (t := beta) le_rfl hb hb hd
  have h3 := moment_tail_real hN (r := beta) (s := beta) (t := beta) hb hb hb hd
  have he : realEndpoint N 1 = 1 := by simp [realEndpoint]
  simp only [he, one_mul, mul_one, Complex.ofReal_one] at h0 h1 h2
  have hid : jointFull N beta D A B C - jointFinite N delta beta D A B C =
      D*(fullMoment N 1 1 1-finiteMoment N delta 1 1 1) +
      A*(fullMoment N 1 1 beta-finiteMoment N delta 1 1 beta) +
      B*(fullMoment N 1 beta beta-finiteMoment N delta 1 beta beta) +
      C*(fullMoment N beta beta beta-finiteMoment N delta beta beta beta) := by
    unfold jointFull jointFinite
    ring
  rw [hid]
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl).trans
  simp only [norm_mul]
  calc
    _ ≤ ‖D‖ * (1 / (Real.pi^3 * delta^2)) +
        ‖A‖ * (realEndpoint N beta / (Real.pi^3 * delta^2)) +
        ‖B‖ * ((realEndpoint N beta * realEndpoint N beta) / (Real.pi^3 * delta^2)) +
        ‖C‖ * ((realEndpoint N beta * realEndpoint N beta * realEndpoint N beta) /
          (Real.pi^3 * delta^2)) := by gcongr
    _ = _ := by unfold jointTail; ring

theorem jointFull_re_lower {N : ℕ} (hN : 0 < N) {beta : ℝ} (hb : beta ≤ 1)
    (D A B C : ℂ) :
    (0.997^2 / 2 : ℝ) * (N : ℝ)^2 *
      boxLower (baseWeight N beta) (realEndpoint N beta) D.re A.re B.re C.re ≤
        (jointFull N beta D A B C).re := by
  let f := fun x : ℝ × ℝ =>
    D.re * simplexWeight N 1 1 1 x + A.re * simplexWeight N 1 1 beta x +
      B.re * simplexWeight N 1 beta beta x + C.re * simplexWeight N beta beta beta x
  have hi0 := (simplexWeight_integrable hN 1 1 1).const_mul D.re
  have hi1 := (simplexWeight_integrable hN 1 1 beta).const_mul A.re
  have hi2 := (simplexWeight_integrable hN 1 beta beta).const_mul B.re
  have hi3 := (simplexWeight_integrable hN beta beta beta).const_mul C.re
  have hi : IntegrableOn f sourceSimplex := ((hi0.add hi1).add hi2).add hi3
  have he : (jointFull N beta D A B C).re = (N : ℝ)^2 * ∫ x in sourceSimplex, f x := by
    have hm0 := fullMoment_real hN 1 1 1
    have hm1 := fullMoment_real hN 1 1 beta
    have hm2 := fullMoment_real hN 1 beta beta
    simp only [Complex.ofReal_one] at hm0 hm1 hm2
    simp only [jointFull, hm0, hm1, hm2, fullMoment_real hN, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have he0 := integral_add hi0 hi1
    have he1 := integral_add (hi0.add hi1) hi2
    have he2 := integral_add ((hi0.add hi1).add hi2) hi3
    simp only [Pi.add_apply] at he0 he1 he2
    dsimp [f]
    rw [he2, he1, he0]
    simp only [integral_const_mul, realMass]
    ring
  have hc : IntegrableOn
      (fun _x : ℝ × ℝ =>
        boxLower (baseWeight N beta) (realEndpoint N beta) D.re A.re B.re C.re)
      sourceSimplex := by
    rw [sourceSimplex_eq_triangle]
    exact continuous_const.continuousOn.integrableOn_compact triangle_isCompact
  have hlo := setIntegral_mono_on hc hi
    (sourceSimplex_eq_triangle ▸ triangle_measurableSet) (fun x hx => ?_)
  · rw [integral_simplex_const] at hlo
    rw [he]
    simpa only [mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hlo (sq_nonneg (N : ℝ))
  · have h := boxLower_le
      (coordinate_weight_bounds hN hb ⟨hx.1, hx.2.1⟩)
      (coordinate_weight_bounds hN hb ⟨hx.2.2.1, hx.2.2.2.1⟩)
      (coordinate_weight_bounds hN hb hx.2.2.2.2) D.re A.re B.re C.re
    dsimp [f, simplexWeight]
    simp only [sub_self, Real.rpow_zero, one_mul, mul_one]
    nlinarith [h]

theorem jointFinite_re_lower {N : ℕ} (hN : 0 < N) {beta delta : ℝ}
    (hb : beta ≤ 1) (hd : 0 < delta) (D A B C : ℂ) :
    (0.997^2 / 2 : ℝ) * (N : ℝ)^2 *
        boxLower (baseWeight N beta) (realEndpoint N beta) D.re A.re B.re C.re -
      jointTail N delta beta D A B C ≤ (jointFinite N delta beta D A B C).re := by
  have he := (Complex.re_le_norm
    (jointFull N beta D A B C - jointFinite N delta beta D A B C)).trans
      (joint_tail_bound hN hb hd D A B C)
  rw [Complex.sub_re] at he
  linarith [jointFull_re_lower hN hb D A B C]

def paidLower (N : ℕ) (delta beta : ℝ) (D A B C : ℂ) : ℝ :=
  (0.997^2 / 2 : ℝ) * (N : ℝ)^2 *
      boxLower (baseWeight N beta) (realEndpoint N beta) D.re A.re B.re C.re -
    jointTail N delta beta D A B C

end LiuWang.Proof.MajorZeroMomentPayment
