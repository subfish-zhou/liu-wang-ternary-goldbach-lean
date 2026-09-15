import LiuWang.Proof.ZeroRegionFamily.Quadratic
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaMultiplicativeValueTransfer

/-! # 不同真实本原实字符的有限尺度排斥：实际四因子正性，无局部余项前提 -/

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer

namespace LiuWang.Proof.ZeroRegionFamily

def datumL (d : PrimitiveQuadraticDatum) : ℂ → ℂ :=
  letI : NeZero d.modulus := ⟨d.modulus_ne⟩
  d.character.LFunction

theorem primitive_real_selected_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1) (hprim : chi.IsPrimitive)
    {beta sigma : ℝ} (hb : 0 < beta) (hz : chi.LFunction (beta : ℂ) = 0)
    (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    -(logDeriv chi.LFunction (sigma : ℂ)).re + 1/(sigma-beta) ≤ Real.log q/2 := by
  obtain ⟨p, hp⟩ := exists_completedZeroIndex_of_LFunction_eq_zero hchi hprim (by simpa) hz
  have hstrip := symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hprim p
  rw [hp] at hstrip
  have hid := primitive_kernel_identity hchi hprim (s := (sigma : ℂ)) (by simpa)
  have hsum := summable_symmetricCompletedLFunction_zeroKernel_re hchi hprim
    (s := (sigma : ℂ)) (by simpa)
  have hh := hsum.le_tsum p (fun r _ => zero_kernel_nonneg hchi hprim (by simpa using hs) r)
  have hk := zeroKernel_re_of_same_im (s := (sigma : ℂ)) (rho := (beta : ℂ))
    (by simpa using ne_of_gt (hstrip.2.trans hs)) (by simp)
  rw [hp, one_div, hk] at hh
  have hg := gamma_real_nonpos chi hs hs2
  simp only [Complex.ofReal_re, one_div] at hh hid ⊢
  linarith

theorem nonprincipal_real_without_zeros_le {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi ≠ 1)
    {sigma : ℝ} (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    -(logDeriv chi.LFunction (sigma : ℂ)).re ≤ 3*Real.log q/2 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hid := primitive_kernel_identity hpr chi.primitiveCharacter_isPrimitive
    (s := (sigma : ℂ)) (by simpa)
  have hz : 0 ≤ ∑' p : SymmetricCompletedZeroIndex chi.primitiveCharacter,
      (1/((sigma : ℂ)-Complex.Hadamard.divisorZeroIndex₀_val p)).re :=
    tsum_nonneg (zero_kernel_nonneg hpr chi.primitiveCharacter_isPrimitive (by simpa using hs))
  have hg := gamma_real_nonpos chi.primitiveCharacter hs hs2
  have hc := norm_logDeriv_LFunction_sub_primitive_le_log chi hchi (s := (sigma : ℂ))
    (by simpa using hs.le)
  have hr := (neg_le_abs (logDeriv chi.LFunction (sigma : ℂ) -
    logDeriv chi.primitiveCharacter.LFunction (sigma : ℂ)).re).trans (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re] at hr
  have hl : Real.log chi.conductor ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast NeZero.pos chi.conductor)
      (by exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  linarith

theorem actual_four_factor_nonneg {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q*r)]
    (chi : DirichletCharacter ℂ q) (psi : DirichletCharacter ℂ r)
    (hc : chi^2=1) (hp : psi^2=1) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ -(logDeriv riemannZeta (sigma : ℂ)).re -
      (logDeriv chi.LFunction (sigma : ℂ)).re -
      (logDeriv psi.LFunction (sigma : ℂ)).re -
      (logDeriv (pairCharacter chi psi).LFunction (sigma : ℂ)).re := by
  have h := fourFactor_negLogDerivative_nonneg chi psi hc hp sigma hs
  have hz : LSeries (fun _ : ℕ => (1 : ℂ)) =
      LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) := by
    congr 1
    funext n
    have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hn]
    simp
  rw [hz] at h
  rw [← (1 : DirichletCharacter ℂ 1).deriv_LFunction_eq_deriv_LSeries (by simpa),
    ← (1 : DirichletCharacter ℂ 1).LFunction_eq_LSeries (by simpa),
    DirichletCharacter.LFunction_modOne_eq,
    ← chi.deriv_LFunction_eq_deriv_LSeries (by simpa),
    ← chi.LFunction_eq_LSeries (by simpa),
    ← psi.deriv_LFunction_eq_deriv_LSeries (by simpa),
    ← psi.LFunction_eq_LSeries (by simpa),
    ← (pairCharacter chi psi).deriv_LFunction_eq_deriv_LSeries (by simpa),
    ← (pairCharacter chi psi).LFunction_eq_LSeries (by simpa)] at h
  simpa only [neg_div, Complex.neg_re, ← logDeriv_apply, sub_eq_add_neg, add_assoc] using h

theorem distinct_data_real_pair_bound (d e : PrimitiveQuadraticDatum) (hde : d ≠ e)
    {beta gamma sigma : ℝ} (hb : 0 < beta) (hg : 0 < gamma)
    (hzb : datumL d (beta : ℂ) = 0) (hzg : datumL e (gamma : ℂ) = 0)
    (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    1/(sigma-beta)+1/(sigma-gamma) ≤ 1/(sigma-1) +
      2*(Real.log d.modulus+Real.log e.modulus) := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let : NeZero e.modulus := ⟨e.modulus_ne⟩
  let : NeZero (d.modulus*e.modulus) := ⟨Nat.mul_ne_zero d.modulus_ne e.modulus_ne⟩
  have hpos := actual_four_factor_nonneg d.character e.character d.square_eq_one e.square_eq_one hs
  have hd := primitive_real_selected_le d.ne_one d.isPrimitive hb hzb hs hs2
  have he := primitive_real_selected_le e.ne_one e.isPrimitive hg hzg hs hs2
  have hp := nonprincipal_real_without_zeros_le (pairCharacter_ne_one_of_datum_ne d e hde) hs hs2
  have hz := ChebyshevBound.HighHeight.zeta_real_le_pole hs hs2
  simp only [neg_div, Complex.neg_re, ← logDeriv_apply] at hz
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast d.modulus_ne) (by exact_mod_cast e.modulus_ne)] at hp
  linarith

theorem real_sources_unique (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x) (hb : 0 < beta) (hg : 0 < gamma)
    (hzb : datumL d (beta : ℂ) = 0) (hzg : datumL e (gamma : ℂ) = 0)
    (hbgap : 1-beta < 1/(24*Real.log x)) (hggap : 1-gamma < 1/(24*Real.log x)) :
    d = e := by
  by_contra hne
  have hL : 1 < Real.log x := by
    apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
    linarith [Real.exp_one_lt_d9]
  have hLd : Real.log d.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast d.modulus_pos) hdx
  have hLe : Real.log e.modulus ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast e.modulus_pos) hex
  have hL0 : 0 < Real.log x := by linarith
  let u := 1/(8*Real.log x)
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; apply (div_le_one (by positivity)).mpr; linarith
  have hLu : Real.log x*u=1/8 := by dsimp [u]; field_simp
  have h := distinct_data_real_pair_bound d e hne hb hg hzb hzg
    (sigma := 1+u) (by linarith) (by linarith)
  rw [show 1+u-1=u by ring, show 1/u=8*Real.log x by dsimp [u]; field_simp] at h
  have hterm (b : ℝ) (hgap : 1-b < 1/(24*Real.log x)) (hzero : b < 1) :
      6*Real.log x < 1/(1+u-b) := by
    have hh := (lt_div_iff₀ (show 0 < 24*Real.log x by positivity)).mp hgap
    apply (lt_div_iff₀ (show 0 < 1+u-b by linarith)).mpr
    nlinarith
  have hb1 : beta < 1 := by
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    by_contra hh
    exact (d.character.LFunction_ne_zero_of_one_le_re (Or.inl d.ne_one) (by simpa using le_of_not_gt hh)) hzb
  have hg1 : gamma < 1 := by
    let : NeZero e.modulus := ⟨e.modulus_ne⟩
    by_contra hh
    exact (e.character.LFunction_ne_zero_of_one_le_re (Or.inl e.ne_one) (by simpa using le_of_not_gt hh)) hzg
  linarith [hterm beta hbgap hb1, hterm gamma hggap hg1]

end LiuWang.Proof.ZeroRegionFamily
