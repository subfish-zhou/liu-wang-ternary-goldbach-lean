import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Family

/-! # 保完整R14，继续加强真实主支与共同来源排斥 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem real_sources_unique_twelve (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ Real.log x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x) (hb : 0 < beta) (hg : 0 < gamma)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hbg : 1-beta < 1/(12*Real.log x)) (hgg : 1-gamma < 1/(12*Real.log x)) : d=e := by
  by_contra hne
  have hL : 0 < Real.log x := by linarith
  have hld : Real.log d.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast d.modulus_pos) hdx
  have hle : Real.log e.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast e.modulus_pos) hex
  let u := 1/(5*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; apply (div_le_one (by positivity)).mpr; linarith
  have huL : Real.log x*u=1/5 := by dsimp [u]; field_simp
  have hh := distinct_sources_real_joint d e hne hb hg hzb hzg
    (sigma := 1+u) (by linarith) (by linarith)
  rw [show 1+u-1=u by ring, show 1/u=5*Real.log x by dsimp [u]; field_simp] at hh
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one) (by simpa using le_of_not_gt h) hzb
  have hg1 : gamma < 1 := by
    let : NeZero e.modulus := ⟨e.modulus_ne⟩
    by_contra h
    exact e.character.LFunction_ne_zero_of_one_le_re (Or.inl e.ne_one) (by simpa using le_of_not_gt h) hzg
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : 1-b < 1/(12*Real.log x)) :
      (60/17)*Real.log x < 1/(1+u-b) := by
    have hh := (lt_div_iff₀ (show 0 < 12*Real.log x by positivity)).mp hgap
    apply (lt_div_iff₀ (show 0 < 1+u-b by linarith)).mpr
    nlinarith only [hh, huL]
  linarith [hterm beta hb1 hbg, hterm gamma hg1 hgg, Real.log_two_lt_d9]

theorem zeta_no_zero_ten {x : ℝ} (hx : 400 ≤ Real.log x) {rho : ℂ}
    (hr : 1-1/(10*Real.log x) < rho.re) (ht : |rho.im| ≤ x) : riemannZeta rho ≠ 0 := by
  have hL : 0 < Real.log x := by linarith
  have hw : 1/(10*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  intro hz
  obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero (by linarith) hz
  have hb := (riemannXiDivisorZeroValue_re_mem_Ioo p).2
  have ht1 := xi_zero_height_gt_one p
  rw [hv] at hb ht1
  let u := 1/(3*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3/20 := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have huL : Real.log x*u=1/3 := by dsimp [u]; field_simp
  have hh := zeta_quartic_core p (by rw [hv]; linarith)
    (sigma := 1+u) (by linarith) (by linarith)
  rw [hv] at hh
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith : 0 < |rho.im|) ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 46630) conductorCoeff_bounds.1)
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL.le
  have hinv : 14379/(1+u-1)=43137*Real.log x := by dsimp [u]; field_simp; ring
  rw [hinv] at hh
  have hupp : 24480/(1+u-rho.re) ≤
      (43137+46630*(691/2500)+139890/400)*Real.log x := by nlinarith only [hh, hl, hk, hx]
  have hp := (div_le_iff₀ (show 0 < 1+u-rho.re by linarith)).mp hupp
  have hgap : (1-rho.re)*Real.log x < 1/10 := by
    have hh := (lt_div_iff₀ (show 0 < 10*Real.log x by positivity)).mp
      (show 1-rho.re < 1/(10*Real.log x) by linarith)
    nlinarith only [hh]
  nlinarith only [hp, hgap, huL]

theorem principal_no_zero_ten {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 400 ≤ Real.log x) {rho : ℂ}
    (hr : 1-1/(10*Real.log x) < rho.re) (ht : |rho.im| ≤ x/(q : ℝ)) (hpole : rho ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction rho ≠ 0 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hx0 : 0 ≤ x := by
    have hh := mul_nonneg ((abs_nonneg _).trans ht) (show (0 : ℝ) ≤ q by positivity)
    simpa only [div_mul_cancel₀ _ (show (q : ℝ) ≠ 0 by positivity)] using hh
  have hw : 1/(10*Real.log x) ≤ 1/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  exact fun hz => zeta_no_zero_ten hx hr (ht.trans (div_le_self hx0 hq))
    ((PrincipalPsi.principal_zero_iff_zeta_zero (by linarith) hpole).mp hz)

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
