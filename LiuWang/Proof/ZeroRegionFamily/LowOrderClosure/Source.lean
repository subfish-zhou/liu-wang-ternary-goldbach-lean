import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Nonprincipal
import LiuWang.Proof.ZeroRegionFamily.LowOrderClosure.Principal

/-! # 全部x>=10的R14真实本原来源排斥 -/

set_option autoImplicit false
noncomputable section

open Complex
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open LiuWang.Proof.ZeroRegionFamily.Uniform

namespace LiuWang.Proof.ZeroRegionFamily.LowOrderClosure

theorem real_sources_unique_fourteen (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x) (hb : 0 < beta) (hg : 0 < gamma)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hbg : 1-beta < 1/(14*Real.log x)) (hgg : 1-gamma < 1/(14*Real.log x)) : d=e := by
  by_contra hne
  have hL := log_scale_ge_34_15 hx
  have hL0 : 0 < Real.log x := by linarith
  have hld : Real.log d.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast d.modulus_pos) hdx
  have hle : Real.log e.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast e.modulus_pos) hex
  let u := 1/(4*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; apply (div_le_one (by positivity)).mpr; linarith
  have huL : Real.log x*u=1/4 := by dsimp [u]; field_simp
  have hh := distinct_sources_real_joint d e hne hb hg hzb hzg
    (sigma := 1+u) (by linarith) (by linarith)
  rw [show 1+u-1=u by ring, show 1/u=4*Real.log x by dsimp [u]; field_simp] at hh
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra h
    exact d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one) (by simpa using le_of_not_gt h) hzb
  have hg1 : gamma < 1 := by
    let : NeZero e.modulus := ⟨e.modulus_ne⟩
    by_contra h
    exact e.character.LFunction_ne_zero_of_one_le_re (Or.inl e.ne_one) (by simpa using le_of_not_gt h) hzg
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : 1-b < 1/(14*Real.log x)) :
      (28/9)*Real.log x < 1/(1+u-b) := by
    have hh := (lt_div_iff₀ (show 0 < 14*Real.log x by positivity)).mp hgap
    apply (lt_div_iff₀ (show 0 < 1+u-b by linarith)).mpr
    nlinarith only [hh, huL]
  have h1 := hterm beta hb1 hbg
  have h2 := hterm gamma hg1 hgg
  linarith [Real.log_two_lt_d9]

end LiuWang.Proof.ZeroRegionFamily.LowOrderClosure
