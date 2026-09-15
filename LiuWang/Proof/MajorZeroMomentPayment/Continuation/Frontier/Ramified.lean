import LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier.DirectPayment

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MeasureTheory
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries LiuWang.Proof.MajorArcApproximation
open LiuWang.Proof.MajorZeroInteraction

namespace LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier

theorem gaussSum_ramified_step {r p : ℕ} [NeZero r] [NeZero (p*r)]
    (hp : p.Prime) (hpr : p ∣ r) (chi : Character r) :
    gaussSum (DirichletCharacter.changeLevel (dvd_mul_left r p) chi) ZMod.stdAddChar = 0 := by
  rw [gaussSum_changeLevel_prime hp]
  have hn : ¬ IsUnit (p : ZMod r) := by
    rw [ZMod.isUnit_iff_coprime]
    exact fun hc => (hp.coprime_iff_not_dvd.mp hc) hpr
  rw [chi.map_nonunit hn, neg_zero, zero_mul]

theorem gaussSum_redundant_prime {q r p : ℕ} [NeZero q] [NeZero r]
    (hp : p.Prime) (hpr : p ∣ r) (hrq : p*r ∣ q) (chi : Character q)
    (hcr : chi.conductor ∣ r) :
    gaussSum chi ZMod.stdAddChar = 0 := by
  let : NeZero (p*r) := ⟨mul_ne_zero hp.ne_zero (NeZero.ne r)⟩
  let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi : Character r := DirichletCharacter.changeLevel hcr chi.primitiveCharacter
  have hz := gaussSum_ramified_step hp hpr psi
  have hb := norm_gaussSum_changeLevel hrq
    (DirichletCharacter.changeLevel (dvd_mul_left r p) psi)
  rw [hz, norm_zero] at hb
  have he : DirichletCharacter.changeLevel hrq
      (DirichletCharacter.changeLevel (dvd_mul_left r p) psi) = chi := by
    dsimp [psi]
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans,
      chi.changeLevel_primitiveCharacter]
  rw [he] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

theorem gaussScale_redundant_prime {q r p : ℕ} [NeZero q] [NeZero r]
    (hp : p.Prime) (hpr : p ∣ r) (hrq : p*r ∣ q) (chi : Character q)
    (hcr : chi.conductor ∣ r) :
    gaussScale chi = 0 := by
  have hc : chi⁻¹.conductor ∣ r := by simpa only [DirichletCharacter.conductor_inv] using hcr
  rw [gaussScale, gaussSum_redundant_prime hp hpr hrq chi⁻¹ hc, mul_zero]

theorem exceptional_coefficients_vanish {N q r p : ℕ} [NeZero q] [NeZero r]
    (hp : p.Prime) (hpr : p ∣ r) (hrq : p*r ∣ q) (chi : Character q)
    (hcr : chi.conductor ∣ r) :
    linearCoefficient N chi = 0 ∧ quadraticCoefficient N chi = 0 ∧ cubicCoefficient N chi = 0 := by
  simp [linearCoefficient, quadraticCoefficient, cubicCoefficient,
    gaussScale_redundant_prime hp hpr hrq chi hcr]

def redundantLevel (d q : ℕ) : Prop :=
  ∃ (p r : ℕ), p.Prime ∧ 0 < r ∧ p ∣ r ∧ p*r ∣ q ∧ d ∣ r

theorem exceptionalArc_redundant_at_witness {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi)
    (hred : redundantLevel chi.conductor q) :
    exceptionalArc N q = 0 := by
  obtain ⟨p, r, hp, hr0, hpr, hrq, hcr⟩ := hred
  let : NeZero r := ⟨hr0.ne'⟩
  have hc := exceptional_coefficients_vanish (N := N) hp hpr hrq chi hcr
  rw [exceptionalArc_eq_joint hN hq hr, hc.1, hc.2.1, hc.2.2]
  simp [jointFinite]

theorem fixed_source_redundant_vanish {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum,
      d.modulus = chi.conductor ∧
      ∀ (s : ℕ) [NeZero s], (s : ℝ) ≤ sourceP N → redundantLevel d.modulus s →
        exceptionalArc N s = 0 := by
  obtain ⟨d, _, hdc, _, _, hall⟩ := exceptionalValues_same_source hN hq hr
  refine ⟨d, hdc, ?_⟩
  intro s _ hs hred
  by_cases hex : ∃ (psi : Character s) (tau : ℂ), tau ∈ exceptionalValues N psi
  · obtain ⟨psi, tau, ht⟩ := hex
    have hcond := (hall s hs psi tau ht).2.1
    exact exceptionalArc_redundant_at_witness hN hs ht (hcond ▸ hred)
  · have hn : ∀ psi : Character s, exceptionalValues N psi = ∅ := by
      intro psi
      exact Finset.eq_empty_iff_forall_notMem.mpr (fun tau ht => hex ⟨psi, tau, ht⟩)
    exact (exceptionalArc_no_exception N hn).1

theorem redundantLevel_ramified_multiplier {d k p : ℕ} (hd : 0 < d)
    (hp : p.Prime) (hpd : p ∣ d) (hpk : p ∣ k) :
    redundantLevel d (k*d) := by
  refine ⟨p, d, hp, hd, hpd, ?_, dvd_refl d⟩
  exact Nat.mul_dvd_mul_right hpk d

theorem redundantLevel_squared_multiplier {d k p : ℕ} (hd : 0 < d)
    (hp : p.Prime) (hpk : p^2 ∣ k) :
    redundantLevel d (k*d) := by
  refine ⟨p, p*d, hp, Nat.mul_pos hp.pos hd, dvd_mul_right p d, ?_, dvd_mul_left d p⟩
  have h := Nat.mul_dvd_mul_right hpk d
  simpa only [pow_two, Nat.mul_assoc] using h

theorem exceptional_redundant_sum_zero {N d : ℕ}
    (hN : Real.exp 2000 ≤ (N : ℝ))
    (hv : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ sourceP N → redundantLevel d q →
      exceptionalArc N q = 0) :
    (∑ q ∈ (denominators (sourceP N)).filter (redundantLevel d), exceptionalArc N q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hq, hred⟩ := Finset.mem_filter.mp hq
  have hp := (mem_denominators (sourceP_pos hN).le q).mp hq
  let : NeZero q := ⟨by omega⟩
  exact hv q hp.2 hred

theorem exceptionalIntegral_prune_redundant {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) :
    ∃ d : PrimitiveQuadraticDatum, d.modulus = chi.conductor ∧
      exceptionalIntegral N =
        ∑ s ∈ (denominators (sourceP N)).filter (fun s => ¬ redundantLevel d.modulus s),
          exceptionalArc N s := by
  obtain ⟨d, hd, hv⟩ := fixed_source_redundant_vanish hN hq hr
  refine ⟨d, hd, ?_⟩
  have hz := exceptional_redundant_sum_zero hN hv
  rw [exceptionalIntegral, coreIndices, Finset.sum_sigma]
  change (∑ s ∈ denominators (sourceP N), exceptionalArc N s) = _
  have he := Finset.sum_filter_add_sum_filter_not
    (denominators (sourceP N)) (redundantLevel d.modulus) (exceptionalArc N)
  rw [hz, zero_add] at he
  exact he.symm

end LiuWang.Proof.MajorZeroMomentPayment.Continuation.Frontier
