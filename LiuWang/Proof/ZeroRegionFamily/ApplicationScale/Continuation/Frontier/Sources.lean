import LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier.FourFactor

/-! # 真实差分四因子与选中实零核：比原常数更宽的同尺度来源排斥 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure

namespace LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier

theorem distinct_sources_damped_bound (d e : PrimitiveQuadraticDatum) (hne : d ≠ e)
    {beta gamma sigma : ℝ} (hb : 1/2 < beta) (hg : 1/2 < gamma)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) :
    1/(sigma-beta)+1/(sigma-gamma) ≤ 1/(sigma-1)+
      2*stechkinConductorCoeff*(Real.log d.modulus+Real.log e.modulus) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let : NeZero e.modulus := ⟨e.modulus_ne⟩
  let : NeZero (d.modulus*e.modulus) := ⟨Nat.mul_ne_zero d.modulus_ne e.modulus_ne⟩
  have hpos := four_factor_stechkin_nonneg d.character e.character d.square_eq_one e.square_eq_one hs
  have hd := primitive_actual_selected_bound d.ne_one d.isPrimitive
    (rho := (beta : ℂ)) (by simpa only [Complex.ofReal_re] using hb) hzb hs hs1
  have he := primitive_actual_selected_bound e.ne_one e.isPrimitive
    (rho := (gamma : ℂ)) (by simpa only [Complex.ofReal_re] using hg) hzg hs hs1
  have hp := imprimitive_damped_bound (pairCharacter d.character e.character)
    (pairCharacter_ne_one_of_datum_ne d e hne) hs hs1 0
  have hj := conductor_euler_refined (pairCharacter d.character e.character) hs
  have hz := zeta_real_strong hs hs1
  have hzero : dampedLogDeriv (1 : DirichletCharacter ℂ 1) sigma (stechkinSigma sigma) stechkinK 0 =
      zetaDamped sigma 0 := by
    simp only [dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq, zetaDamped]
  rw [hzero] at hpos
  simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, max_eq_left zero_le_one, Real.log_one] at hd he hp
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast d.modulus_ne) (by exact_mod_cast e.modulus_ne)] at hj
  have hpi := mul_le_mul_of_nonneg_left log_pi_ge_one conductorCoeff_bounds.1
  have hk := conductorCoeff_lower
  nlinarith

theorem real_sources_unique_eight (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hbg : 1-beta < 1/(8*Real.log x)) (hgg : 1-gamma < 1/(8*Real.log x)) : d=e := by
  by_contra hne
  have hL := log_scale_ge_34_15 hx
  have hL0 : 0 < Real.log x := by linarith
  have hld : Real.log d.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast d.modulus_pos) hdx
  have hle : Real.log e.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast e.modulus_pos) hex
  have hw : 1/(8*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  let u := (3/10)/Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by dsimp [u]; apply (div_le_iff₀ hL0).mpr; linarith
  have huL : Real.log x*u=3/10 := by dsimp [u]; field_simp
  have hh := distinct_sources_damped_bound d e hne (by linarith) (by linarith) hzb hzg
    (sigma := 1+u) (by linarith) (by linarith)
  rw [show 1+u-1=u by ring, show 1/u=(10/3)*Real.log x by dsimp [u]; field_simp] at hh
  have hm := mul_le_mul_of_nonneg_left (show Real.log d.modulus+Real.log e.modulus ≤ 2*Real.log x by linarith)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one) (by simpa using le_of_not_gt h) hzb
  have hg1 : gamma < 1 := by
    let : NeZero e.modulus := ⟨e.modulus_ne⟩
    by_contra h
    exact e.character.LFunction_ne_zero_of_one_le_re (Or.inl e.ne_one) (by simpa using le_of_not_gt h) hzg
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : 1-b < 1/(8*Real.log x)) :
      (40/17)*Real.log x < 1/(1+u-b) := by
    have hh := (lt_div_iff₀ (show 0 < 8*Real.log x by positivity)).mp hgap
    apply (lt_div_iff₀ (show 0 < 1+u-b by linarith)).mpr
    nlinarith only [hh, huL]
  have h1 := hterm beta hb1 hbg
  have h2 := hterm gamma hg1 hgg
  nlinarith

theorem real_sources_unique_original (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hbg : 1-beta < 1/(9.645908801*Real.log x))
    (hgg : 1-gamma < 1/(9.645908801*Real.log x)) : d=e := by
  have hL : 0 < Real.log x := by linarith [log_scale_ge_34_15 hx]
  have hw : 1/(9.645908801*Real.log x) ≤ 1/(8*Real.log x) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact real_sources_unique_eight d e hx hdx hex hzb hzg (hbg.trans_le hw) (hgg.trans_le hw)

end LiuWang.Proof.ZeroRegionFamily.ApplicationScale.Continuation.Frontier
