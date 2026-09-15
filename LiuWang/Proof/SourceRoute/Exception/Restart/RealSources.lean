import LiuWang.Proof.SourceRoute.Exception.Restart.DampedFourFactor

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.ApplicationScale

namespace LiuWang.Proof.SourceRoute.Exception.Restart

theorem distinct_sources_damped_bound (d e : PrimitiveQuadraticDatum) (hne : d ≠ e)
    {beta gamma sigma : ℝ} (hb : 1 / 2 < beta) (hg : 1 / 2 < gamma)
    (hzb : datumL d (beta : ℂ) = 0) (hzg : datumL e (gamma : ℂ) = 0)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    1 / (sigma - beta) + 1 / (sigma - gamma) ≤ 1 / (sigma - 1) +
      2 * stechkinConductorCoeff * (Real.log d.modulus + Real.log e.modulus) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let : NeZero e.modulus := ⟨e.modulus_ne⟩
  let : NeZero (d.modulus * e.modulus) := ⟨Nat.mul_ne_zero d.modulus_ne e.modulus_ne⟩
  have hpos := four_factor_stechkin_nonneg d.character e.character
    d.square_eq_one e.square_eq_one hs
  have hd := primitive_actual_selected_bound d.ne_one d.isPrimitive hb hzb hs hs1
  have he := primitive_actual_selected_bound e.ne_one e.isPrimitive hg hzg hs hs1
  have hp := imprimitive_damped_bound (pairCharacter d.character e.character)
    (pairCharacter_ne_one_of_datum_ne d e hne) hs hs1 0
  have hc := conductor_euler_refined (pairCharacter d.character e.character) hs
  have hz := principal_real_strong (q := 1) hs hs1
  have hpi := mul_le_mul_of_nonneg_left ChebyshevBound.HighHeight.log_pi_ge_one
    conductorCoeff_bounds.1
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast d.modulus_ne)
    (by exact_mod_cast e.modulus_ne)] at hc
  simp only [Complex.ofReal_im, abs_zero, max_eq_left zero_le_one, Real.log_one,
    add_zero, Complex.ofReal_re] at hd he hp
  have hz0 : principalPrimeCost 1 sigma = 0 := by simp [principalPrimeCost]
  rw [hz0, sub_zero] at hz
  nlinarith [conductorCoeff_lower]

theorem real_sources_unique_eight (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x) (hb : 1 / 2 < beta) (hg : 1 / 2 < gamma)
    (hzb : datumL d (beta : ℂ) = 0) (hzg : datumL e (gamma : ℂ) = 0)
    (hbg : 1 - beta ≤ 1 / (8 * Real.log x))
    (hgg : 1 - gamma ≤ 1 / (8 * Real.log x)) : d = e := by
  by_contra hne
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  have hld := Real.log_le_log (Nat.cast_pos.mpr d.modulus_pos) hdx
  have hle := Real.log_le_log (Nat.cast_pos.mpr e.modulus_pos) hex
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one)
      (by simpa using le_of_not_gt h) hzb
  have hg1 : gamma < 1 := by
    let : NeZero e.modulus := ⟨e.modulus_ne⟩
    by_contra h
    exact e.character.LFunction_ne_zero_of_one_le_re (Or.inl e.ne_one)
      (by simpa using le_of_not_gt h) hzg
  let u := (3 / 10) / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3 / 20 := by
    dsimp [u]
    apply (div_le_iff₀ hL0).mpr
    linarith
  have huL : u * Real.log x = 3 / 10 := by dsimp [u]; field_simp
  have hh := distinct_sources_damped_bound d e hne hb hg hzb hzg
    (sigma := 1 + u) (by linarith) (by linarith)
  have hinv : 1 / (1 + u - 1) = (10 / 3) * Real.log x := by
    dsimp [u]
    field_simp
    ring
  rw [hinv] at hh
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : 1 - b ≤ 1 / (8 * Real.log x)) :
      (40 / 17) * Real.log x ≤ 1 / (1 + u - b) := by
    have hh := (le_div_iff₀ (show 0 < 8 * Real.log x by positivity)).mp hgap
    apply (le_div_iff₀ (show 0 < 1 + u - b by linarith)).mpr
    nlinarith only [hh, huL]
  have h1 := hterm beta hb1 hbg
  have h2 := hterm gamma hg1 hgg
  have hlogs := mul_le_mul_of_nonneg_left (add_le_add hld hle)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  nlinarith only [hh, h1, h2, hlogs, hk, hL0]

theorem original_re_half {x beta : ℝ} (hx : 10 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) : 1 / 2 < beta := by
  have hL := log_scale_ge hx
  have hw : 1 / (9.645908801 * Real.log x) < 1 / 2 :=
    (div_lt_iff₀ (by positivity)).mpr (by linarith)
  linarith

theorem real_sources_unique_original (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hg : 1 - 1 / (9.645908801 * Real.log x) ≤ gamma)
    (hzb : datumL d (beta : ℂ) = 0) (hzg : datumL e (gamma : ℂ) = 0) : d = e := by
  have hL := log_scale_ge hx
  have hw : 1 / (9.645908801 * Real.log x) ≤ 1 / (8 * Real.log x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact real_sources_unique_eight d e hx hdx hex (original_re_half hx hb)
    (original_re_half hx hg) hzb hzg (by linarith) (by linarith)

end LiuWang.Proof.SourceRoute.Exception.Restart
