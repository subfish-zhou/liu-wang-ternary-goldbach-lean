import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.CriticalBounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.MajorZeroMomentPayment LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

def multiplicity : PureKind → ℕ
  | .linear => 1
  | .quadratic => 2
  | .cubic => 3

def momentCoefficient : PureKind → ℝ
  | .linear => 2.8959
  | .quadratic => 3*quadraticHolderConstant
  | .cubic => 3*1.0302*1.0033^2/Real.pi

def paidMassCoefficient : PureKind → ℝ
  | .linear => 2.826575
  | .quadratic => 2.826575
  | .cubic => 3.390828

def numerator (r : ℝ) : PureKind → ℝ
  | .linear => Real.sqrt r
  | .quadratic => r
  | .cubic => r*Real.sqrt r

def muFactor (d : ℕ) : PureKind → ℝ
  | .linear => moebiusWeight d
  | .quadratic => moebiusWeight d
  | .cubic => 1

def summedCoefficient : PureKind → ℝ
  | .linear => 2.8959*2.826575
  | .quadratic => 8.2907
  | .cubic => 3.35785

def pureCostBudget : PureKind → ℝ
  | .linear => 0.00002099
  | .quadratic => 0.0010299
  | .cubic => 0.093965

def originalPureCostBudget : PureKind → ℝ
  | .linear => 0.000021
  | .quadratic => 0.00108
  | .cubic => 0.09403

theorem multiplicity_cast (j : PureKind) : (multiplicity j : ℝ) = zeroPower j := by
  cases j <;> norm_num [multiplicity, zeroPower]

theorem muFactor_bounds (d : ℕ) (j : PureKind) : 0 ≤ muFactor d j ∧ muFactor d j ≤ 1 := by
  have hm : 0 ≤ moebiusWeight d ∧ moebiusWeight d ≤ 1 := by
    rw [moebiusWeight_eq]
    split_ifs <;> norm_num
  cases j <;> simp [muFactor, hm]

theorem numerator_rpow (j : PureKind) {r : ℝ} (hr : 0 < r) :
    r^(-decayPower j)*r^2 = numerator r j := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
  cases j with
  | linear =>
    norm_num [decayPower, numerator]
    rw [← Real.sqrt_eq_rpow]
  | quadratic => norm_num [decayPower, numerator]
  | cubic =>
    rw [show -decayPower .cubic+(2 : ℕ) = (1 : ℝ)+1/2 by norm_num [decayPower],
      Real.rpow_add hr, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rfl

theorem conductor_ratio_identity (j : PureKind) {r : ℝ} (hr : 0 < r) (phi : ℝ) :
    numerator r j/phi^2 = r^(-decayPower j)*(r/phi)^2 := by
  rw [div_pow, ← mul_div_assoc, numerator_rpow j hr]

theorem paid_cost_identity (N d : ℕ) (beta : ℝ) (j : PureKind) (hd : 0 < d) :
    sourceMomentFactor N beta j*paidArithmeticFactor d j =
      (momentCoefficient j*paidMassCoefficient j)*(N : ℝ)^2 *
        (muFactor d j * ((d : ℝ)^(-decayPower j)*((d : ℝ)/(d.totient : ℝ))^2 *
          baseWeight N beta^(multiplicity j))) := by
  rw [← conductor_ratio_identity j (by exact_mod_cast hd)]
  cases j <;>
    dsimp [sourceMomentFactor, paidArithmeticFactor, momentCoefficient, paidMassCoefficient,
      muFactor, numerator, multiplicity] <;> ring

theorem beta_gap_power {N : ℕ} {r beta : ℝ} (hN : Real.exp 3100 ≤ (N : ℝ))
    (hgap : Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2) ≤ 1-beta)
    (j : PureKind) :
    baseWeight N beta^(multiplicity j) ≤
      Real.exp (-(zeroPower j*Real.pi*sourceL N)/
        (0.4923*Real.sqrt r*(Real.log r)^2)) := by
  have hn : 0 < (N : ℝ) := (Real.exp_pos _).trans_le hN
  have hl : 0 ≤ sourceL N := by linarith [sourceL_ge_3100 hN]
  have hk : 0 ≤ (multiplicity j : ℝ) := Nat.cast_nonneg _
  rw [baseWeight, Real.rpow_def_of_pos hn, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg (show 0 ≤ zeroPower j by rw [← multiplicity_cast]; exact hk) hl)
  rw [multiplicity_cast]
  change zeroPower j*(sourceL N*(beta-1)) ≤ _
  rw [show -(zeroPower j*Real.pi*sourceL N)/(0.4923*Real.sqrt r*(Real.log r)^2) =
    -(zeroPower j*sourceL N*(Real.pi/(0.4923*Real.sqrt r*(Real.log r)^2))) by ring]
  nlinarith

theorem paid_cost_scalar (j : PureKind) {N d : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hd : 0 < d)
    (hphi : (d : ℝ)/(d.totient : ℝ) ≤ nu d)
    (hgap : Real.pi/(0.4923*Real.sqrt d*(Real.log d)^2) ≤ 1-beta) :
    sourceMomentFactor N beta j*paidArithmeticFactor d j ≤
      (momentCoefficient j*paidMassCoefficient j)*(N : ℝ)^2 *
        conductorScalar j d (sourceL N) := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have hph0 : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hratio : 0 ≤ (d : ℝ)/(d.totient : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hratio hphi 2
  have hb := beta_gap_power hN hgap j
  have hp : 0 ≤ (d : ℝ)^(-decayPower j) := Real.rpow_nonneg hd0.le _
  have hbase : 0 ≤ baseWeight N beta^(multiplicity j) := by dsimp [baseWeight]; positivity
  have hc0 : 0 ≤ (momentCoefficient j*paidMassCoefficient j)*(N : ℝ)^2 := by
    cases j <;> dsimp [momentCoefficient, paidMassCoefficient, quadraticHolderConstant] <;> positivity
  rw [paid_cost_identity N d beta j hd]
  apply mul_le_mul_of_nonneg_left _ hc0
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hpow hp) hb hbase (by positivity)
  have hm := mul_le_mul_of_nonneg_right (muFactor_bounds d j).2
    (show 0 ≤ (d : ℝ)^(-decayPower j)*((d : ℝ)/(d.totient : ℝ))^2*
      baseWeight N beta^(multiplicity j) by positivity)
  simp only [one_mul] at hm
  exact hm.trans h

theorem moment_mass_coefficient_bound (j : PureKind) :
    momentCoefficient j*paidMassCoefficient j ≤ summedCoefficient j := by
  cases j with
  | linear => rfl
  | quadratic =>
    dsimp [momentCoefficient, paidMassCoefficient, summedCoefficient, quadraticHolderConstant]
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 3*Real.pi)).mpr
    nlinarith [Real.pi_gt_d20]
  | cubic =>
    dsimp [momentCoefficient, paidMassCoefficient, summedCoefficient]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_d20]

theorem pure_decimal_payment (j : PureKind) :
    summedCoefficient j*certifiedValue j ≤ pureCostBudget j ∧
      pureCostBudget j ≤ originalPureCostBudget j := by
  cases j <;> norm_num [summedCoefficient, certifiedValue, pureCostBudget, originalPureCostBudget]

theorem paid_cost_numeric (j : PureKind) {N d : ℕ} {beta : ℝ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hdomain : paperDomain d (sourceL N))
    (hphi : (d : ℝ)/(d.totient : ℝ) ≤ nu d)
    (hgap : Real.pi/(0.4923*Real.sqrt d*(Real.log d)^2) ≤ 1-beta) :
    sourceMomentFactor N beta j*paidArithmeticFactor d j ≤ pureCostBudget j*(N : ℝ)^2 := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := by linarith [hdomain.1]
    exact_mod_cast this
  have hscalar := paper_scalar_stronger j hdomain
  have hp0 : 0 ≤ conductorScalar j d (sourceL N) := by dsimp [conductorScalar]; positivity
  have hc0 : 0 ≤ summedCoefficient j := by cases j <;> norm_num [summedCoefficient]
  calc
    _ ≤ (momentCoefficient j*paidMassCoefficient j)*(N : ℝ)^2*
        conductorScalar j d (sourceL N) := paid_cost_scalar j hN hd hphi hgap
    _ ≤ summedCoefficient j*(N : ℝ)^2*certifiedValue j :=
      mul_le_mul (mul_le_mul_of_nonneg_right (moment_mass_coefficient_bound j) (sq_nonneg _))
        hscalar hp0 (mul_nonneg hc0 (sq_nonneg _))
    _ ≤ pureCostBudget j*(N : ℝ)^2 := by
      nlinarith [mul_le_mul_of_nonneg_right (pure_decimal_payment j).1 (sq_nonneg (N : ℝ))]

theorem actual_pure_totals_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hdomain : paperDomain chi.conductor (sourceL N))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor)
    (hgap : Real.pi/(0.4923*Real.sqrt chi.conductor*(Real.log chi.conductor)^2) ≤ 1-rho.re) :
    ∀ j : PureKind,
      (∑ s ∈ denominators (sourceP N), ‖selectedPureArc N s j‖) ≤
        pureCostBudget j*(N : ℝ)^2 := by
  obtain ⟨d, hd, hall⟩ := fixed_source_pure_totals_paid (exp_2000_le_of_exp_3100_le hN) hq hr
  intro j
  rw [hd] at hall
  exact (hall j).trans (paid_cost_numeric j hN hdomain hphi hgap)

theorem actual_pure_integrals_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hdomain : paperDomain chi.conductor (sourceL N))
    (hphi : (chi.conductor : ℝ)/(chi.conductor.totient : ℝ) ≤ nu chi.conductor)
    (hgap : Real.pi/(0.4923*Real.sqrt chi.conductor*(Real.log chi.conductor)^2) ≤ 1-rho.re) :
    ∀ j : PureKind, ‖selectedPureIntegral N j‖ ≤ pureCostBudget j*(N : ℝ)^2 := by
  intro j
  exact (norm_sum_le _ _).trans (actual_pure_totals_numeric hN hq hr hdomain hphi hgap j)

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
