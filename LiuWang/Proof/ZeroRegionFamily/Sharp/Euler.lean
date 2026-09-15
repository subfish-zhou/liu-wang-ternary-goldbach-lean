import LiuWang.Proof.ZeroRegionFamily.Sharp.EulerScalar
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalHighStripLogDerivativeBound

/-! # 普通字符和主字符的实际同权重坏素数费用 -/

set_option autoImplicit false
noncomputable section

open Complex Finset
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.ZeroRegionFamily.Sharp

def primeCost (p : ℕ) (sigma : ℝ) : ℝ :=
  Real.log p*((p : ℝ)^(-sigma)/(1-(p : ℝ)^(-sigma))-
    stechkinK*(p : ℝ)^(-stechkinSigma sigma)/(1-(p : ℝ)^(-stechkinSigma sigma)))

theorem primePower_parameters {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ (p : ℝ)^(-sigma) ∧
    (p : ℝ)^(-stechkinSigma sigma) ≤ (p : ℝ)^(-sigma) ∧
    0 ≤ (p : ℝ)^(-stechkinSigma sigma) ∧ (p : ℝ)^(-sigma) < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨by positivity, Real.rpow_le_rpow_of_exponent_le hp1.le
    (neg_le_neg (stechkinSigma_ge hs)), by positivity, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

theorem primeCost_nonneg {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma) :
    0 ≤ primeCost p sigma := by
  obtain ⟨ha, hab, hb, ha1⟩ := primePower_parameters hp hs
  exact mul_nonneg (Real.log_natCast_nonneg _)
    (geometric_cost_nonneg ha hab hb ha1 stechkinK_mem)

theorem primeCost_eq_positive_power {p : ℕ} (hp : p.Prime) (sigma : ℝ) :
    primeCost p sigma = Real.log p*(1/((p : ℝ)^sigma-1)-
      stechkinK/((p : ℝ)^(stechkinSigma sigma)-1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have he (s : ℝ) : (p : ℝ)^(-s)/(1-(p : ℝ)^(-s))=1/((p : ℝ)^s-1) := by
    rw [Real.rpow_neg hp0.le]
    have hn := (Real.rpow_pos_of_pos hp0 s).ne'
    by_cases hh : (p : ℝ)^s=1
    · simp [hh]
    · field_simp
  unfold primeCost
  rw [he]
  have hh := he (stechkinSigma sigma)
  rw [mul_div_assoc, hh]
  ring

theorem cpow_geometric_bound {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hs : 1 < sigma)
    (t : ℝ) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    ‖c*(p : ℂ)^(-((sigma : ℂ)+Complex.I*t))/
        (1-c*(p : ℂ)^(-((sigma : ℂ)+Complex.I*t)))-
      (stechkinK : ℂ)*(c*(p : ℂ)^(-((stechkinSigma sigma : ℂ)+Complex.I*t))/
        (1-c*(p : ℂ)^(-((stechkinSigma sigma : ℂ)+Complex.I*t))))‖ ≤
      (p : ℝ)^(-sigma)/(1-(p : ℝ)^(-sigma))-
        stechkinK*(p : ℝ)^(-stechkinSigma sigma)/(1-(p : ℝ)^(-stechkinSigma sigma)) := by
  obtain ⟨ha, hab, hb, ha1⟩ := primePower_parameters hp hs
  have hz : ‖c*(p : ℂ)^(-(Complex.I*t))‖ ≤ 1 := by
    have hphase : ‖(p : ℂ)^(-(Complex.I*t))‖ = 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
        (by exact_mod_cast hp.pos)]
      norm_num [Complex.mul_re]
    simpa [norm_mul, hphase] using hc
  have hh := norm_geometric_difference_le ha hab hb ha1 stechkinK_mem hz
  rw [natCast_cpow_neg_add_I_mul hp.ne_zero, natCast_cpow_neg_add_I_mul hp.ne_zero]
  convert hh using 1
  congr 1
  ring

theorem norm_factor_difference_le {q p : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hp : p.Prime)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    ‖logDeriv (levelCorrectionFactor chi p) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (levelCorrectionFactor chi p)
        ((stechkinSigma sigma : ℂ)+Complex.I*t)‖ ≤ primeCost p sigma := by
  have hh := cpow_geometric_bound hp hs t (DirichletCharacter.norm_le_one chi.primitiveCharacter p)
  rw [logDeriv_levelCorrectionFactor, logDeriv_levelCorrectionFactor]
  unfold levelCorrectionFactor primeCost
  have he (s s1 : ℂ) :
      chi.primitiveCharacter p*(Real.log p : ℂ)*(p : ℂ)^(-s)/(1-chi.primitiveCharacter p*(p : ℂ)^(-s))-
        (stechkinK : ℂ)*(chi.primitiveCharacter p*(Real.log p : ℂ)*(p : ℂ)^(-s1)/
          (1-chi.primitiveCharacter p*(p : ℂ)^(-s1))) =
        (Real.log p : ℂ)*(chi.primitiveCharacter p*(p : ℂ)^(-s)/(1-chi.primitiveCharacter p*(p : ℂ)^(-s))-
          (stechkinK : ℂ)*(chi.primitiveCharacter p*(p : ℂ)^(-s1)/(1-chi.primitiveCharacter p*(p : ℂ)^(-s1)))) := by
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_left hh (Real.log_natCast_nonneg _)

def badPrimeCost {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (sigma : ℝ) : ℝ :=
  ∑ p ∈ q.primeFactors, if chi.primitiveCharacter p=0 then 0 else primeCost p sigma

def principalPrimeCost (q : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ q.primeFactors, primeCost p sigma

theorem norm_level_difference_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    ‖logDeriv (levelCorrection chi) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (levelCorrection chi) ((stechkinSigma sigma : ℂ)+Complex.I*t)‖ ≤
      badPrimeCost chi sigma := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hs0 : 1 ≤ ((sigma : ℂ)+Complex.I*t).re := by simpa [Complex.mul_re] using hs.le
  have hs1 : 1 ≤ ((stechkinSigma sigma : ℂ)+Complex.I*t).re := by
    simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le
  rw [logDeriv_levelCorrection_eq_sum chi hc hs0, logDeriv_levelCorrection_eq_sum chi hc hs1,
    mul_sum, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  split_ifs with hz
  · simp [logDeriv_levelCorrectionFactor, hz]
  · exact norm_factor_difference_le chi (Nat.prime_of_mem_primeFactors hp) hs t

theorem imprimitive_damped_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hc : chi ≠ 1)
    {sigma : ℝ} (hs : 1 < sigma) (hs1 : sigma ≤ 23/20) (t : ℝ) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK t ≤
      stechkinConductorCoeff*(Real.log chi.conductor+Real.log (max 1 |t|)-Real.log Real.pi)+
        4/15+badPrimeCost chi sigma := by
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
  have hh := primitive_damped_bound hpr chi.primitiveCharacter_isPrimitive hs hs1 t
  have he := norm_level_difference_le chi hc hs t
  have hr := (neg_le_abs
    (logDeriv (levelCorrection chi) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (levelCorrection chi) ((stechkinSigma sigma : ℂ)+Complex.I*t)).re).trans
    (Complex.abs_re_le_norm _)
  unfold dampedLogDeriv at *
  rw [logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [Complex.mul_re] using hs.le),
    logDeriv_LFunction_eq_primitive_add_levelCorrection chi hc
      (by simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le)]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at *
  linarith

theorem norm_principal_factor_difference_le {p : ℕ} (hp : p.Prime)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    ‖logDeriv (principalLevelCorrectionFactor p) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (principalLevelCorrectionFactor p)
        ((stechkinSigma sigma : ℂ)+Complex.I*t)‖ ≤ primeCost p sigma := by
  have hh := cpow_geometric_bound hp hs t (c := 1) (by simp)
  simp only [one_mul] at hh
  rw [logDeriv_principalLevelCorrectionFactor, logDeriv_principalLevelCorrectionFactor]
  unfold principalLevelCorrectionFactor primeCost
  have he (z w : ℂ) :
      (Real.log p : ℂ)*z/(1-z)-(stechkinK : ℂ)*((Real.log p : ℂ)*w/(1-w)) =
        (Real.log p : ℂ)*(z/(1-z)-(stechkinK : ℂ)*(w/(1-w))) := by ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_left hh (Real.log_natCast_nonneg _)

theorem norm_principal_level_difference_le (q : ℕ)
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    ‖logDeriv (principalLevelCorrection q) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (principalLevelCorrection q) ((stechkinSigma sigma : ℂ)+Complex.I*t)‖ ≤
      principalPrimeCost q sigma := by
  rw [logDeriv_principalLevelCorrection_eq_sum (by simpa [Complex.mul_re] using hs.le),
    logDeriv_principalLevelCorrection_eq_sum
      (by simpa [Complex.mul_re] using (hs.trans_le (stechkinSigma_ge hs)).le),
    mul_sum, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  exact norm_principal_factor_difference_le (Nat.prime_of_mem_primeFactors hp) hs t

theorem principal_damped_euler_bound {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) (t : ℝ) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t ≤
      -(logDeriv riemannZeta ((sigma : ℂ)+Complex.I*t)).re+
        stechkinK*(logDeriv riemannZeta ((stechkinSigma sigma : ℂ)+Complex.I*t)).re+
        principalPrimeCost q sigma := by
  have he := norm_principal_level_difference_le q hs t
  have hr := (neg_le_abs
    (logDeriv (principalLevelCorrection q) ((sigma : ℂ)+Complex.I*t)-
      (stechkinK : ℂ)*logDeriv (principalLevelCorrection q) ((stechkinSigma sigma : ℂ)+Complex.I*t)).re).trans
    (Complex.abs_re_le_norm _)
  unfold dampedLogDeriv
  rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta (by simpa [Complex.mul_re] using hs),
    logDeriv_principal_eq_levelCorrection_add_riemannZeta
      (by simpa [Complex.mul_re] using hs.trans_le (stechkinSigma_ge hs))]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at *
  linarith

theorem principal_real_correction_eq (q : ℕ) (sigma : ℝ) (hs : 1 < sigma) :
    (logDeriv (principalLevelCorrection q) (sigma : ℂ)).re-
      stechkinK*(logDeriv (principalLevelCorrection q) (stechkinSigma sigma : ℂ)).re =
      principalPrimeCost q sigma := by
  rw [logDeriv_principalLevelCorrection_eq_sum (by simpa using hs.le),
    logDeriv_principalLevelCorrection_eq_sum
      (by simpa using (hs.trans_le (stechkinSigma_ge hs)).le)]
  simp only [Complex.re_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpower (u : ℝ) : (p : ℂ)^(-(u : ℂ)) = (((p : ℝ)^(-u) : ℝ) : ℂ) := by
    have hh := natCast_cpow_neg_add_I_mul hpp.ne_zero u 0
    simpa using hh
  rw [logDeriv_principalLevelCorrectionFactor, logDeriv_principalLevelCorrectionFactor]
  simp only [principalLevelCorrectionFactor, hpower, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  dsimp [primeCost]
  ring

theorem principal_real_damped_identity {q : ℕ} [NeZero q]
    {sigma : ℝ} (hs : 1 < sigma) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK 0 =
      -(logDeriv riemannZeta (sigma : ℂ)).re+
        stechkinK*(logDeriv riemannZeta (stechkinSigma sigma : ℂ)).re-
        principalPrimeCost q sigma := by
  have he := principal_real_correction_eq q sigma hs
  simp only [dampedLogDeriv, Complex.ofReal_zero, mul_zero, add_zero]
  rw [logDeriv_principal_eq_levelCorrection_add_riemannZeta (by simpa using hs),
    logDeriv_principal_eq_levelCorrection_add_riemannZeta
      (by simpa using hs.trans_le (stechkinSigma_ge hs))]
  simp only [Complex.add_re]
  linarith

end LiuWang.Proof.ZeroRegionFamily.Sharp
