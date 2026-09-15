import LiuWang.Proof.ZeroRegionFamily.Uniform.Quadratic

/-! # 实轴联合导子付款与不同本原实来源的R16排斥 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open BombieriVinogradov.SiegelWalfisz
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ZeroRegionFamily.RealClosure
open scoped Classical

namespace LiuWang.Proof.ZeroRegionFamily.Uniform

theorem norm_level_factor_le_prime_fraction {q p : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (levelCorrectionFactor chi p) s‖ ≤ Real.log p/(p-1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow : ‖(p : ℂ)^(-s)‖ ≤ 1/(p : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_re_ne_zero p (by rw [Complex.neg_re]; linarith)]
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_le hp1.le (show (-s).re ≤ -1 by simp; linarith)
  have hprod : ‖chi.primitiveCharacter p*(p : ℂ)^(-s)‖ ≤ 1/(p : ℝ) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one chi.primitiveCharacter p)
      (norm_nonneg _)).trans (by simpa using hpow)
  have hi : 1/(p : ℝ) < 1 := (div_lt_one hp0).mpr hp1
  have hden : 1-1/(p : ℝ) ≤ ‖levelCorrectionFactor chi p s‖ := by
    have hr := norm_sub_norm_le (1 : ℂ) (chi.primitiveCharacter p*(p : ℂ)^(-s))
    simp only [norm_one] at hr
    change _ ≤ ‖1-chi.primitiveCharacter p*(p : ℂ)^(-s)‖
    linarith
  have hnum : ‖chi.primitiveCharacter p*(Real.log p : ℂ)*(p : ℂ)^(-s)‖ ≤ Real.log p/(p : ℝ) := by
    rw [show chi.primitiveCharacter p*(Real.log p : ℂ)*(p : ℂ)^(-s)=
      (Real.log p : ℂ)*(chi.primitiveCharacter p*(p : ℂ)^(-s)) by ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hprod (Real.log_natCast_nonneg p)
  rw [logDeriv_levelCorrectionFactor, norm_div]
  calc
    _ ≤ (Real.log p/(p : ℝ))/(1-1/(p : ℝ)) :=
      div_le_div₀ (by positivity) hnum (by linarith) hden
    _ = Real.log p/((p : ℝ)-1) := by field_simp

theorem sum_prime_fraction_le (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, Real.log p/(p-1)) ≤ (∑ p ∈ s, Real.log p)/2+Real.log 2/2 := by
  have hh := sum_le_sum (fun (p : ℕ) (h : p ∈ s) => show Real.log p/(p-1) ≤
      Real.log p/2+(if p=2 then Real.log 2/2 else 0) from by
    by_cases h2 : p=2
    · subst p; norm_num
    · have hp3 : 3 ≤ p := by have := (hp p h).two_le; omega
      have hp2 : (2 : ℝ) ≤ (p : ℝ)-1 := by
        have h : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      simp only [h2, if_false, add_zero]
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by norm_num) hp2)
  have h2 : (∑ p ∈ s, if p=2 then Real.log 2/2 else 0) ≤ Real.log 2/2 := by
    simp only [sum_ite_eq']
    split_ifs <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  rw [sum_add_distrib, ← sum_div] at hh
  linarith

theorem real_conductor_correction_joint {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    Real.log chi.conductor/2+‖logDeriv (levelCorrection chi) s‖ ≤ Real.log q/2+Real.log 2/2 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let f := q.primeFactors.filter (fun p : ℕ => chi.primitiveCharacter p ≠ 0)
  have hsub : f ⊆ q.primeFactors := filter_subset _ _
  have hp : ∀ p ∈ f, p.Prime := fun p h => Nat.prime_of_mem_primeFactors (hsub h)
  have he : (∑ p ∈ q.primeFactors, logDeriv (levelCorrectionFactor chi p) s) =
      ∑ p ∈ f, logDeriv (levelCorrectionFactor chi p) s := by
    unfold f
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    split_ifs with h
    · rfl
    · have hv : chi.primitiveCharacter p=0 := not_not.mp h
      simp [logDeriv_levelCorrectionFactor, hv]
  have hn : ‖logDeriv (levelCorrection chi) s‖ ≤ ∑ p ∈ f, Real.log p/(p-1) := by
    rw [logDeriv_levelCorrection_eq_sum chi hc hs, he]
    exact (norm_sum_le _ _).trans (sum_le_sum (fun p h => norm_level_factor_le_prime_fraction chi (hp p h) hs))
  have hl := missing_prime_log_mass chi.conductor_ne_zero chi.conductor_dvd_level f hsub
    (fun p h => badPrime_support_missing chi (hp p h) (mem_filter.mp h).2)
  have hh := sum_prime_fraction_le f hp
  linarith

theorem nonprincipal_real_joint {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) {sigma : ℝ} (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    -(logDeriv chi.LFunction (sigma : ℂ)).re ≤ Real.log q/2+Real.log 2/2 := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hid := primitive_kernel_identity hpr chi.primitiveCharacter_isPrimitive
    (s := (sigma : ℂ)) (by simpa)
  have hz : 0 ≤ ∑' p : SymmetricCompletedZeroIndex chi.primitiveCharacter,
      (1/((sigma : ℂ)-Complex.Hadamard.divisorZeroIndex₀_val p)).re :=
    tsum_nonneg (zero_kernel_nonneg hpr chi.primitiveCharacter_isPrimitive (by simpa using hs))
  have hg := gamma_real_nonpos chi.primitiveCharacter hs hs2
  have hj := real_conductor_correction_joint chi hc (s := (sigma : ℂ)) hs.le
  have hn := (neg_le_abs (logDeriv (levelCorrection chi) (sigma : ℂ)).re).trans (Complex.abs_re_le_norm _)
  rw [logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc hs.le, Complex.add_re]
  linarith

theorem distinct_sources_real_joint (d e : PrimitiveQuadraticDatum) (hne : d ≠ e)
    {beta gamma sigma : ℝ} (hb : 0 < beta) (hg : 0 < gamma)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hs : 1 < sigma) (hs2 : sigma ≤ 2) :
    1/(sigma-beta)+1/(sigma-gamma) ≤ 1/(sigma-1)+
      Real.log d.modulus+Real.log e.modulus+Real.log 2/2 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  let : NeZero e.modulus := ⟨e.modulus_ne⟩
  let : NeZero (d.modulus*e.modulus) := ⟨Nat.mul_ne_zero d.modulus_ne e.modulus_ne⟩
  have hpos := actual_four_factor_nonneg d.character e.character d.square_eq_one e.square_eq_one hs
  have hd := primitive_real_selected_le d.ne_one d.isPrimitive hb hzb hs hs2
  have he := primitive_real_selected_le e.ne_one e.isPrimitive hg hzg hs hs2
  have hp := nonprincipal_real_joint (pairCharacter d.character e.character)
    (pairCharacter_ne_one_of_datum_ne d e hne) hs hs2
  have hz := ChebyshevBound.HighHeight.zeta_real_le_pole hs hs2
  simp only [neg_div, Complex.neg_re, ← logDeriv_apply] at hz
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast d.modulus_ne) (by exact_mod_cast e.modulus_ne)] at hp
  linarith

theorem real_sources_unique_sixteen (d e : PrimitiveQuadraticDatum)
    {x beta gamma : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hex : (e.modulus : ℝ) ≤ x) (hb : 0 < beta) (hg : 0 < gamma)
    (hzb : datumL d (beta : ℂ)=0) (hzg : datumL e (gamma : ℂ)=0)
    (hbg : 1-beta < 1/(16*Real.log x)) (hgg : 1-gamma < 1/(16*Real.log x)) : d=e := by
  by_contra hne
  have hL := log_scale_ge hx
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
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : 1-b < 1/(16*Real.log x)) :
      (16/5)*Real.log x < 1/(1+u-b) := by
    have hh := (lt_div_iff₀ (show 0 < 16*Real.log x by positivity)).mp hgap
    apply (lt_div_iff₀ (show 0 < 1+u-b by linarith)).mpr
    nlinarith
  have h1 := hterm beta hb1 hbg
  have h2 := hterm gamma hg1 hgg
  linarith [Real.log_two_lt_d9]

end LiuWang.Proof.ZeroRegionFamily.Uniform
