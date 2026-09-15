import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption.MixedFinite

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.MajorZeroInteraction
open LiuWang.Proof.MajorZeroMomentPayment
open LiuWang.Proof.MajorZeroMomentPayment.Continuation

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption

def regularLowValues {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : Finset ℂ :=
  (regularValues N chi).filter (fun rho => |rho.im| ≤ omegaCutoff N q)

def regularHighValues {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : Finset ℂ :=
  (regularValues N chi).filter (fun rho => omegaCutoff N q < |rho.im|)

def regularLowMass {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  ∑ rho ∈ regularLowValues N chi, (analyticOrderNatAt chi.LFunction rho : ℝ)*lowWeight N rho

def regularHighMass {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  ∑ rho ∈ regularHighValues N chi, (analyticOrderNatAt chi.LFunction rho : ℝ)*highWeight N rho

def regularMass {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  ∑ rho ∈ regularValues N chi, (analyticOrderNatAt chi.LFunction rho : ℝ)*regularWeight N q rho

theorem regularMass_low_high {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    regularMass N chi = regularLowMass N chi+5*regularHighMass N chi := by
  simp only [regularMass, regularLowMass, regularHighMass, regularLowValues,
    regularHighValues, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  unfold regularWeight
  by_cases h : |rho.im| ≤ omegaCutoff N q
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h]
    ring

theorem regularValue_re_pos {N q : ℕ} [NeZero q]
    {chi : Character q} {rho : ℂ} (hr : rho ∈ regularValues N chi) : 0 < rho.re :=
  (mem_zeroValues.mp (Finset.mem_filter.mp hr).1).2.1

theorem regularMass_nonneg {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) : 0 ≤ regularMass N chi :=
  Finset.sum_nonneg (fun _rho hr => mul_nonneg (Nat.cast_nonneg _)
    (regularWeight_pos hN (NeZero.pos q) (regularValue_re_pos hr)).le)

theorem regularValues_erase_exceptional {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    regularValues N chi = zeroValues chi (sourceT N) \ exceptionalValues N chi := by
  ext rho
  simp only [regularValues, exceptionalValues, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem actual_regular_deletion {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ} (hr : rho ∈ exceptionalValues N chi) (psi : Character q) :
    regularValues N psi =
      if psi = chi then (zeroValues psi (sourceT N)).erase rho else zeroValues psi (sourceT N) := by
  rw [regularValues_erase_exceptional]
  split_ifs with hc
  · subst psi
    rw [exceptionalValues_at_witness hN hq hr, Finset.sdiff_singleton_eq_erase]
  · rw [exceptionalValues_other_character hN hq hr hc, Finset.sdiff_empty]

theorem actual_high_deletion_empty {N q : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (chi : Character q) :
    regularHighValues N chi =
      (zeroValues chi (sourceT N)).filter (fun rho => omegaCutoff N q < |rho.im|) := by
  ext rho
  simp only [regularHighValues, regularValues, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hz, hh⟩
    refine ⟨⟨hz, ?_⟩, hh⟩
    intro hreg
    have hr : rho ∈ exceptionalValues N chi := Finset.mem_filter.mpr ⟨hz, hreg⟩
    have hi := (exceptionalValues_quadratic_simple hN hq hr).2.2.1
    rw [hi, abs_zero] at hh
    linarith [omegaCutoff_pos hN (NeZero.pos q)]

theorem norm_regularAmplitude {q : ℕ} [NeZero q] (chi : Character q) (rho : ℂ) :
    ‖regularAmplitude chi rho‖ =
      ‖gaussScale chi‖*(analyticOrderNatAt chi.LFunction rho : ℝ) := by
  simp only [regularAmplitude, norm_mul, Complex.norm_natCast]

theorem sum_amplitude_scale {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    (∑ rho ∈ regularValues N chi, ‖regularAmplitude chi rho‖*regularScale N q rho) =
      ‖gaussScale chi‖*radiusRoot N q*(regularLowMass N chi+5*regularHighMass N chi) := by
  rw [← regularMass_low_high]
  simp only [regularMass, Finset.mul_sum, norm_regularAmplitude, regularScale]
  apply Finset.sum_congr rfl
  intro rho _
  ring

def phaseMass {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  ∑ psi : Character q, ‖phaseCoefficient N (chi*psi)‖*‖gaussScale psi‖*regularMass N psi

def pairPhaseMass {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) : ℝ :=
  ∑ psi : Character q, ∑ tau : Character q,
    ‖phaseCoefficient N (chi*psi*tau)‖*‖gaussScale psi‖*‖gaussScale tau‖*
      regularMass N psi*regularMass N tau

theorem phaseMass_low_high {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    phaseMass N chi =
      ∑ psi : Character q, ‖phaseCoefficient N (chi*psi)‖*‖gaussScale psi‖*
        (regularLowMass N psi+5*regularHighMass N psi) := by
  simp only [phaseMass, regularMass_low_high]

theorem pairPhaseMass_low_high {q : ℕ} [NeZero q] (N : ℕ) (chi : Character q) :
    pairPhaseMass N chi =
      ∑ psi : Character q, ∑ tau : Character q,
        ‖phaseCoefficient N (chi*psi*tau)‖*‖gaussScale psi‖*‖gaussScale tau‖*
          (regularLowMass N psi+5*regularHighMass N psi)*
          (regularLowMass N tau+5*regularHighMass N tau) := by
  simp only [pairPhaseMass, regularMass_low_high]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.SourceConsumption
