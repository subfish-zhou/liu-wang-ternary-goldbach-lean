import LiuWang.Proof.MajorZeroMomentPayment.Tail

/-! Real mixed moments have positive full-axis mass. The actual finite-radius
lower bound includes the paid tail; no favorable finite-arc sign is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.MajorZeroMomentPayment

def baseWeight (N : ℕ) (beta : ℝ) : ℝ := (N : ℝ) ^ (beta - 1)

def simplexWeight (N : ℕ) (r s t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ((N : ℝ) * x.1)^(r - 1) * ((N : ℝ) * x.2)^(s - 1) *
    ((N : ℝ) * (1 - x.1 - x.2))^(t - 1)

def realMass (N : ℕ) (r s t : ℝ) : ℝ :=
  (N : ℝ)^2 * ∫ x in sourceSimplex, simplexWeight N r s t x

theorem real_cpow {x beta : ℝ} (hx : 0 ≤ x) :
    (x : ℂ)^((beta : ℂ) - 1) = (x^(beta - 1) : ℝ) := by
  rw [Complex.ofReal_cpow hx]
  push_cast
  rfl

theorem simplexWeight_ofReal {N : ℕ} (_hN : 0 < N) (r s t : ℝ)
    {x : ℝ × ℝ} (hx : x ∈ sourceSimplex) :
    (simplexWeight N r s t x : ℂ) =
      (((N : ℝ) * x.1 : ℝ) : ℂ)^((r : ℂ) - 1) *
      (((N : ℝ) * x.2 : ℝ) : ℂ)^((s : ℂ) - 1) *
      (((N : ℝ) * (1 - x.1 - x.2) : ℝ) : ℂ)^((t : ℂ) - 1) := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [real_cpow (mul_nonneg hn (by linarith [hx.1])),
    real_cpow (mul_nonneg hn (by linarith [hx.2.2.1])),
    real_cpow (mul_nonneg hn (by linarith [hx.2.2.2.2.1]))]
  simp only [simplexWeight, Complex.ofReal_mul]

theorem fullMoment_real {N : ℕ} (hN : 0 < N) (r s t : ℝ) :
    fullMoment N r s t = (realMass N r s t : ℂ) := by
  rw [fullMoment_eq_simplex hN]
  unfold realMass
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun (sourceSimplex_eq_triangle ▸ triangle_measurableSet)
  intro x hx
  simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_natCast] using (simplexWeight_ofReal hN r s t hx).symm

theorem simplexWeight_integrable {N : ℕ} (hN : 0 < N) (r s t : ℝ) :
    IntegrableOn (simplexWeight N r s t) sourceSimplex := by
  have hi := (simplex_cpow_integrableOn (N : ℝ) (Nat.cast_pos.mpr hN)
    (r : ℂ) (s : ℂ) (t : ℂ)).re
  rw [← sourceSimplex_eq_triangle] at hi
  apply hi.congr
  filter_upwards [ae_restrict_mem (sourceSimplex_eq_triangle ▸ triangle_measurableSet)] with x hx
  exact congrArg Complex.re (simplexWeight_ofReal hN r s t hx).symm

theorem coordinate_weight_bounds {N : ℕ} (hN : 0 < N) {beta x : ℝ}
    (hb : beta ≤ 1) (hx : x ∈ Icc (0.001 : ℝ) 1) :
    baseWeight N beta ≤ ((N : ℝ) * x)^(beta - 1) ∧
      ((N : ℝ) * x)^(beta - 1) ≤ realEndpoint N beta := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  constructor
  · exact Real.rpow_le_rpow_of_nonpos (mul_pos hn (by linarith [hx.1]))
      (by nlinarith [hx.2]) (by linarith)
  · exact Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 0.001 * (N : ℝ))
      (by nlinarith [hx.1]) (by linarith)

theorem simplexWeight_bounds {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) {x : ℝ × ℝ}
    (hx : x ∈ sourceSimplex) :
    baseWeight N r * baseWeight N s * baseWeight N t ≤ simplexWeight N r s t x ∧
      simplexWeight N r s t x ≤ realEndpoint N r * realEndpoint N s * realEndpoint N t := by
  have h₁ := coordinate_weight_bounds hN hr ⟨hx.1, hx.2.1⟩
  have h₂ := coordinate_weight_bounds hN hs ⟨hx.2.2.1, hx.2.2.2.1⟩
  have h₃ := coordinate_weight_bounds hN ht hx.2.2.2.2
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hp₁ : 0 ≤ (N : ℝ) * x.1 := mul_nonneg hn (by linarith [hx.1])
  have hp₂ : 0 ≤ (N : ℝ) * x.2 := mul_nonneg hn (by linarith [hx.2.2.1])
  have hp₃ : 0 ≤ (N : ℝ) * (1 - x.1 - x.2) := mul_nonneg hn (by linarith [hx.2.2.2.2.1])
  dsimp [simplexWeight]
  constructor
  · apply mul_le_mul (mul_le_mul h₁.1 h₂.1 (by unfold baseWeight; positivity)
      (by positivity)) h₃.1 (by unfold baseWeight; positivity) (by positivity)
  · apply mul_le_mul (mul_le_mul h₁.2 h₂.2 (by positivity)
      (by unfold realEndpoint; positivity)) h₃.2 (by positivity)
      (by unfold realEndpoint; positivity)

theorem integral_simplex_const (c : ℝ) :
    (∫ _x in sourceSimplex, c) = (0.997^2 / 2 : ℝ) * c := by
  simp only [setIntegral_const, smul_eq_mul, measureReal_def, sourceSimplex_volume]
  rw [ENNReal.toReal_ofReal (by positivity)]

theorem realMass_bounds {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    (0.997^2 / 2 : ℝ) * (N : ℝ)^2 *
        (baseWeight N r * baseWeight N s * baseWeight N t) ≤ realMass N r s t ∧
      realMass N r s t ≤ (0.997^2 / 2 : ℝ) * (N : ℝ)^2 *
        (realEndpoint N r * realEndpoint N s * realEndpoint N t) := by
  have hmeas : MeasurableSet sourceSimplex := sourceSimplex_eq_triangle ▸ triangle_measurableSet
  have hc (c : ℝ) : IntegrableOn (fun _x : ℝ × ℝ => c) sourceSimplex := by
    rw [sourceSimplex_eq_triangle]
    exact continuous_const.continuousOn.integrableOn_compact triangle_isCompact
  have hlo := setIntegral_mono_on (hc (baseWeight N r * baseWeight N s * baseWeight N t))
    (simplexWeight_integrable hN r s t) hmeas
    (fun x hx => (simplexWeight_bounds hN hr hs ht hx).1)
  have hhi := setIntegral_mono_on (simplexWeight_integrable hN r s t)
    (hc (realEndpoint N r * realEndpoint N s * realEndpoint N t)) hmeas
    (fun x hx => (simplexWeight_bounds hN hr hs ht hx).2)
  rw [integral_simplex_const] at hlo hhi
  constructor
  · simpa only [realMass, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hlo (sq_nonneg (N : ℝ))
  · simpa only [realMass, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hhi (sq_nonneg (N : ℝ))

theorem finiteMoment_re_lower {N : ℕ} (hN : 0 < N) {r s t : ℝ}
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) {delta : ℝ} (hd : 0 < delta) :
    (0.997^2 / 2 : ℝ) * (N : ℝ)^2 *
        (baseWeight N r * baseWeight N s * baseWeight N t) -
      realEndpoint N r * realEndpoint N s * realEndpoint N t / (Real.pi^3 * delta^2) ≤
        (finiteMoment N delta r s t).re := by
  have h := (Complex.re_le_norm (fullMoment N r s t - finiteMoment N delta r s t)).trans
    (moment_tail_real hN hr hs ht hd)
  rw [fullMoment_real hN r s t, Complex.sub_re, Complex.ofReal_re] at h
  linarith [(realMass_bounds hN hr hs ht).1]

theorem endpoint_le_thirtytwo {N : ℕ} {beta : ℝ} (hb : 1/2 ≤ beta) :
    realEndpoint N beta ≤ 32 * baseWeight N beta := by
  have hc : (0.001 : ℝ)^(beta - 1) ≤ 32 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 0.001)
      (by norm_num : (0.001 : ℝ) ≤ 1) (show -(1/2 : ℝ) ≤ beta - 1 by linarith)
    have he : (0.001 : ℝ)^(-(1/2 : ℝ)) = Real.sqrt 1000 := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
      norm_num
    rw [he] at h
    exact h.trans ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
  rw [realEndpoint, Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
  simpa only [baseWeight, mul_comm] using
    mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg N) (beta - 1))

theorem actual_tail_le_small {N q : ℕ} (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    (hsmall : (q : ℝ) ≤ sourceP N / 1000) {r s t : ℝ}
    (hr : 1/2 ≤ r ∧ r ≤ 1) (hs : 1/2 ≤ s ∧ s ≤ 1) (ht : 1/2 ≤ t ∧ t ≤ 1) :
    ‖fullMoment N r s t - finiteMoment N (deltaRadius N q) r s t‖ ≤
      0.1 * (N : ℝ)^2 * (baseWeight N r * baseWeight N s * baseWeight N t) := by
  have hP := sourceP_pos hN
  have hratio : 0 ≤ (q : ℝ) / sourceP N := by positivity
  have hratio' : (q : ℝ) / sourceP N ≤ 1/1000 := by
    apply (div_le_iff₀ hP).mpr
    linarith
  have hc : (100 : ℝ) / (3.36^2 * Real.pi) ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hu := mul_le_mul
    (mul_le_mul (endpoint_le_thirtytwo (N := N) hr.1) (endpoint_le_thirtytwo (N := N) hs.1)
      (by unfold realEndpoint; positivity) (by unfold baseWeight; positivity))
    (endpoint_le_thirtytwo (N := N) ht.1) (by unfold realEndpoint; positivity)
    (by unfold baseWeight; positivity)
  apply (actual_radius_tail_real hN hq hr.2 hs.2 ht.2).trans
  calc
    _ ≤ 3 * (1/1000 : ℝ)^2 * (N : ℝ)^2 *
        ((32 * baseWeight N r) * (32 * baseWeight N s) * (32 * baseWeight N t)) := by
      apply mul_le_mul _ hu (by unfold realEndpoint; positivity) (by positivity)
      gcongr
    _ ≤ _ := by
      have hp : 0 ≤ (N : ℝ)^2 * (baseWeight N r * baseWeight N s * baseWeight N t) := by
        unfold baseWeight
        positivity
      nlinarith

theorem actual_mixed_moment_positive {N q : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : 0 < q)
    (hsmall : (q : ℝ) ≤ sourceP N / 1000) {r s t : ℝ}
    (hr : 1/2 ≤ r ∧ r ≤ 1) (hs : 1/2 ≤ s ∧ s ≤ 1) (ht : 1/2 ≤ t ∧ t ≤ 1) :
    0.39 * (N : ℝ)^2 * (baseWeight N r * baseWeight N s * baseWeight N t) ≤
      (finiteMoment N (deltaRadius N q) r s t).re := by
  have he := (Complex.re_le_norm
    (fullMoment N r s t - finiteMoment N (deltaRadius N q) r s t)).trans
      (actual_tail_le_small hN hq hsmall hr hs ht)
  rw [fullMoment_real (nat_pos_of_exp_le hN) r s t, Complex.sub_re, Complex.ofReal_re] at he
  have hm := (realMass_bounds (nat_pos_of_exp_le hN) hr.2 hs.2 ht.2).1
  have hp : 0 ≤ (N : ℝ)^2 * (baseWeight N r * baseWeight N s * baseWeight N t) := by
    unfold baseWeight
    positivity
  nlinarith

end LiuWang.Proof.MajorZeroMomentPayment
