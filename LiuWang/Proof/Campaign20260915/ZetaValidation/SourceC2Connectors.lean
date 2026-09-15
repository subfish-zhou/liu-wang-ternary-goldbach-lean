import LiuWang.Proof.Campaign20260915.ZetaValidation.SourceC2Integral

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology Interval

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsC2LeftAbscissa (eta : ℝ) (m : ℕ) (T : ℝ) : ℝ :=
  -((m : ℝ) + 1 / 2) -
    (((m : ℝ) + 1 / 2 + (rsC2Corner eta).re) / (rsC2Corner eta).im) * T

theorem rsC2Right_depth (eta T : ℝ) :
    rsDescentPoint eta (Real.sqrt 2 * T) = ((eta + T : ℝ) : ℂ) - T * I := by
  unfold rsDescentPoint rsDescentDirection
  push_cast
  field_simp
  ring

theorem rsC2Left_depth {eta : ℝ} (he : 0 < eta) (m : ℕ) (T : ℝ) :
    rsC2LeftPoint eta m (1 + T / (rsC2Corner eta).im) =
      (rsC2LeftAbscissa eta m T : ℂ) - T * I := by
  have hn := (rsC2Corner_upper he).2.ne'
  apply Complex.ext
  · rw [(rsC2LeftPoint_coordinates _ _ _).1]
    simp only [rsC2LeftAbscissa, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero]
    field_simp
    ring
  · rw [(rsC2LeftPoint_coordinates _ _ _).2]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_sub]
    field_simp
    ring

theorem rsHankel_horizontal_connector_bound {s : ℂ} (m : ℕ) (hs : s.re ≤ 1)
    (a b : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ x : ℝ in a..b, rsHankelKernel s m (x - T * I)‖ ≤
      |b - a| * (Real.exp (2 * Real.pi * |s.im|) * Real.exp (-(2 * Real.pi * m) * T)) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp (2 * Real.pi * |s.im|) * Real.exp (-(2 * Real.pi * m) * T))
    (a := a) (b := b) (fun x _ => by
      have hh := rsHankelKernel_lower_bound m hs (z := (x : ℂ) - T * I) (by simp; linarith)
      simpa [neg_mul, mul_neg] using hh)
  simpa [mul_comm] using h

theorem rsHankel_affine_connector_limit {s : ℂ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) (a b c d : ℝ) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (a * T + b)..(c * T + d),
      rsHankelKernel s m (x - T * I)) atTop (𝓝 0) := by
  have hc : 0 < 2 * Real.pi * (m : ℝ) := by positivity
  have he : Tendsto (fun T : ℝ => Real.exp (-(2 * Real.pi * m) * T)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hTe : Tendsto (fun T : ℝ => T * Real.exp (-(2 * Real.pi * m) * T)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) _ hc
  have hlim := ((hTe.const_mul (|c - a|)).add (he.const_mul |d - b|)).const_mul
    (Real.exp (2 * Real.pi * |s.im|))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have habs : |(c * T + d) - (a * T + b)| ≤ |c - a| * T + |d - b| := by
    calc
      _ = |(c - a) * T + (d - b)| := by congr 1; ring
      _ ≤ |(c - a) * T| + |d - b| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (show 0 ≤ T by linarith)]
  calc
    _ ≤ _ := rsHankel_horizontal_connector_bound m hs _ _ hT
    _ ≤ (|c - a| * T + |d - b|) *
        (Real.exp (2 * Real.pi * |s.im|) * Real.exp (-(2 * Real.pi * m) * T)) :=
      mul_le_mul_of_nonneg_right habs (by positivity)
    _ = _ := by ring

theorem rsC2_connectors_limit {s : ℂ} {eta : ℝ} {m : ℕ} (hm : 0 < m)
    (hs : s.re ≤ 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in T..(eta + T),
      rsHankelKernel s m (x - T * I)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-T)..(rsC2LeftAbscissa eta m T),
      rsHankelKernel s m (x - T * I)) atTop (𝓝 0) := by
  constructor
  · simpa only [one_mul, add_zero, add_comm] using
      rsHankel_affine_connector_limit hm hs 1 0 1 eta
  · simpa only [rsC2LeftAbscissa, neg_one_mul, add_zero, sub_eq_add_neg, neg_mul,
      one_mul, zero_add, add_comm] using
      rsHankel_affine_connector_limit hm hs (-1) 0
        (-(((m : ℝ) + 1 / 2 + (rsC2Corner eta).re) / (rsC2Corner eta).im)) (-((m : ℝ) + 1 / 2))

theorem rsC2_connectors_integrable {s : ℂ} {eta T : ℝ} (he : 0 < eta) (hT : 0 < T) (m : ℕ) :
    IntervalIntegrable (fun x : ℝ => rsHankelKernel s m (x - T * I)) volume T (eta + T) ∧
    IntervalIntegrable (fun x : ℝ => rsHankelKernel s m (x - T * I)) volume
      (-T) (rsC2LeftAbscissa eta m T) := by
  have aux {a b : ℝ} (hab : ∀ x ∈ uIcc a b, x ≠ 0) :
      IntervalIntegrable (fun x : ℝ => rsHankelKernel s m (x - T * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) - T * I)
      (rsHankelKernel_analytic s m (z := (x : ℂ) - T * I) (by simpa using hab x hx) ?_).continuousAt
    · fun_prop
    · rintro ⟨n, hn⟩
      have hi := congrArg Complex.im hn
      simp at hi
      linarith
  constructor
  · apply aux
    intro x hx
    rw [uIcc_of_le (by linarith : T ≤ eta + T)] at hx
    linarith [hx.1]
  · have hb : rsC2LeftAbscissa eta m T < 0 := by
      unfold rsC2LeftAbscissa
      have hh : 0 < (((m : ℝ) + 1 / 2 + (rsC2Corner eta).re) /
          (rsC2Corner eta).im) * T := by
        obtain ⟨hcR, hcI⟩ := rsC2Corner_upper he
        positivity
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    apply aux
    intro x hx
    have hx' : x ≤ max (-T) (rsC2LeftAbscissa eta m T) := hx.2
    have hmax : max (-T) (rsC2LeftAbscissa eta m T) < 0 := max_lt (by linarith) hb
    linarith

end LiuWang.Proof.Campaign20260915.ZetaValidation
