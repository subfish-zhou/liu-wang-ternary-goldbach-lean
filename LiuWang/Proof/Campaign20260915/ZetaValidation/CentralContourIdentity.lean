import LiuWang.Proof.Campaign20260915.ZetaValidation.CentralPathIntegrals

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsCentralLogCutoff (T : ℝ) : ℝ := Real.log (Real.sqrt 2 * T)

def rsCentralCircularTruncation (s : ℂ) (m : ℕ) (R T : ℝ) : ℂ :=
  -(∫ x : ℝ in (Real.log R)..(rsCentralLogCutoff T),
      rsHankelLift s m (x + (-(Real.pi / 4) : ℝ) * I)) +
    rsHankelArcBetween s m (Real.log R) (-(Real.pi / 4)) (5 * Real.pi / 4) +
    ∫ x : ℝ in (Real.log R)..(rsCentralLogCutoff T),
      rsHankelLift s m (x + (5 * Real.pi / 4 : ℝ) * I)

def rsCentralSourceTruncation (s : ℂ) (m : ℕ) (eta T : ℝ) : ℂ :=
  -(∫ y : ℝ in (-eta / 2)..(Real.sqrt 2 * T), rsC2RightIntegrand s eta m y) +
    ∫ r : ℝ in 0..(1 + T / (rsC2Corner eta).im), rsC2LeftIntegrand s eta m r

theorem rsCentral_ray_endpoints {T : ℝ} (hT : 0 < T) :
    exp ((rsCentralLogCutoff T : ℂ) + (-(Real.pi / 4) : ℝ) * I) = (T : ℂ) - T * I ∧
    exp ((rsCentralLogCutoff T : ℂ) + (5 * Real.pi / 4 : ℝ) * I) = -(T : ℂ) - T * I := by
  have hpos : 0 < Real.sqrt 2 * T := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hθ : 5 * Real.pi / 4 = Real.pi / 4 + Real.pi := by ring
  constructor <;> apply Complex.ext <;>
    simp [rsCentralLogCutoff, exp_re, exp_im, Real.exp_log hpos, hθ,
      Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
    nlinarith

theorem rsCentral_horizontal_integral (s : ℂ) (m : ℕ) {a b T : ℝ} (hT : 0 < T)
    (hx : ∀ x ∈ uIcc a b, x ≠ 0) :
    (∫ x : ℝ in a..b, rsHankelKernel s m (x - T * I)) =
      rsCentralPrimitive s m (b - T * I) - rsCentralPrimitive s m (a - T * I) := by
  have h := rsCentral_line_integral s m (-(T : ℂ) * I) 1
    (a := a) (b := b) (fun x hx' => by
      simpa only [mul_one, neg_mul, sub_eq_add_neg, add_comm] using
        rsCentral_horizontal_mem (m := m) (hx x hx') hT)
  simpa only [mul_one, one_mul, neg_mul, sub_eq_add_neg, add_comm] using h

theorem rsCentralCircularTruncation_primitive (s : ℂ) (m : ℕ) {R T : ℝ}
    (hR : (m : ℝ) < R) (hR' : R < m + 1) (hT : 0 < T) :
    rsCentralCircularTruncation s m R T =
      rsCentralPrimitive s m (-(T : ℂ) - T * I) -
        rsCentralPrimitive s m ((T : ℂ) - T * I) := by
  have hr := rsCentral_ray_integral s m (Real.log R) (rsCentralLogCutoff T)
    (θ := -(Real.pi / 4)) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (lt_of_le_of_lt (rsHankel_right_sector_sin ⟨by linarith [Real.pi_pos], le_rfl⟩) (by norm_num))
  have hl := rsCentral_ray_integral s m (Real.log R) (rsCentralLogCutoff T)
    (θ := 5 * Real.pi / 4) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (lt_of_le_of_lt (rsHankel_left_sector_sin ⟨le_rfl, by linarith [Real.pi_pos]⟩) (by norm_num))
  rw [(rsCentral_ray_endpoints hT).1] at hr
  rw [(rsCentral_ray_endpoints hT).2] at hl
  rw [rsCentralCircularTruncation, hr, hl, rsCentral_arc_integral s m hR hR']
  ring

theorem rsCentralSourceTruncation_primitive (s : ℂ) {m : ℕ} {eta T : ℝ}
    (hlo : (m : ℝ) < eta) (hhi : eta < m + 1) (hT : 0 < T) :
    rsCentralSourceTruncation s m eta T =
      rsCentralPrimitive s m ((rsC2LeftAbscissa eta m T : ℂ) - T * I) -
        rsCentralPrimitive s m (((eta + T : ℝ) : ℂ) - T * I) := by
  have he : 0 < eta := lt_of_le_of_lt (Nat.cast_nonneg m) hlo
  have hb : -eta / 2 ≤ Real.sqrt 2 * T := by
    have hh : 0 < Real.sqrt 2 * T := by positivity
    linarith
  rw [rsCentralSourceTruncation, rsCentral_right_integral s hlo hhi hb,
    rsCentral_left_integral s he m, rsC2Right_depth, rsC2Left_depth he]
  ring

theorem rsCentral_finite_contour_identity (s : ℂ) {m : ℕ} {eta R T : ℝ}
    (hlo : (m : ℝ) < eta) (hhi : eta < m + 1)
    (hR : (m : ℝ) < R) (hR' : R < m + 1) (hT : 0 < T) :
    rsCentralCircularTruncation s m R T = rsCentralSourceTruncation s m eta T +
      (∫ x : ℝ in T..(eta + T), rsHankelKernel s m (x - T * I)) -
        ∫ x : ℝ in (-T)..(rsC2LeftAbscissa eta m T), rsHankelKernel s m (x - T * I) := by
  have he : 0 < eta := lt_of_le_of_lt (Nat.cast_nonneg m) hlo
  have hr := rsCentral_horizontal_integral s m (a := T) (b := eta + T) hT (fun x hx => by
    rw [uIcc_of_le (by linarith : T ≤ eta + T)] at hx
    linarith [hx.1])
  have hb : rsC2LeftAbscissa eta m T < 0 := by
    unfold rsC2LeftAbscissa
    obtain ⟨hcR, hcI⟩ := rsC2Corner_upper he
    have hh : 0 < (((m : ℝ) + 1 / 2 + (rsC2Corner eta).re) / (rsC2Corner eta).im) * T := by
      positivity
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hl := rsCentral_horizontal_integral s m (a := -T) (b := rsC2LeftAbscissa eta m T)
    hT (fun x hx => by
      have hmax : max (-T) (rsC2LeftAbscissa eta m T) < 0 := max_lt (by linarith) hb
      have hx' : x ≤ max (-T) (rsC2LeftAbscissa eta m T) := hx.2
      linarith)
  rw [rsCentralCircularTruncation_primitive s m hR hR' hT,
    rsCentralSourceTruncation_primitive s hlo hhi hT, hr, hl]
  push_cast
  ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
