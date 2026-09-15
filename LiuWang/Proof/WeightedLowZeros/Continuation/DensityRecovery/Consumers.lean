import LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery.Counts
import LiuWang.Proof.WeightedLowZeros.Continuation.PacketNumerics

/-! # Original numerical and S/Jrho consumers with both table counts discharged -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery

theorem r24_retained_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) :
    retainedSum N q (omegaCutoff N q) d e ≤ 8.2e-10 / sourceL N :=
  exceptional_density_budget hN hq d e hd (retainedCount_bulk_paid hN hq d e)
    (retainedCount_033_paid hN hq d e) hregion

theorem paper_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) :
    lowSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 8.2e-10 / sourceL N :=
  paper_source_numeric_from_density hN hq hd (retainedCount_bulk_paid hN hq d e)
    (retainedCount_033_paid hN hq d e) hregion

theorem full_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N :=
  nonexceptional_density_budget hN hq (familyCount_bulk_paid hN hq)
    (familyCount_033_paid hN hq) h2 hregion

theorem cut_Jrho_le {N q : ℕ} [NeZero q] (hN : 0 < N)
    (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q)) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ Z chi,
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤ (N : ℝ) * cutMass N q Z := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => subset_Jrho_le hN chi (omegaCutoff N q) eta (Z chi) (hZ chi))
  simpa only [cutMass, ← Finset.mul_sum] using h

theorem r24_Jrho_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤ (N : ℝ) * (8.2e-10 / sourceL N) :=
  (cut_Jrho_le (nat_pos_of_exp_le hN) _ (fun _ => Finset.filter_subset _ _) eta).trans
    (mul_le_mul_of_nonneg_left (r24_retained_numeric hN hq hd hregion) (Nat.cast_nonneg _))

theorem paper_Jrho_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤ (N : ℝ) * (8.2e-10 / sourceL N) :=
  paper_source_Jrho_numeric hN hq hd (retainedCount_bulk_paid hN hq d e)
    (retainedCount_033_paid hN hq d e) hregion eta

theorem full_Jrho_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤ (N : ℝ) * (0.0194 / sourceL N) :=
  (cut_Jrho_le (nat_pos_of_exp_le hN) _ (fun _ _ hr => hr) eta).trans
    (mul_le_mul_of_nonneg_left (full_numeric hN hq h2 hregion) (Nat.cast_nonneg _))

theorem paper_packet_numeric {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    ‖retainedPacket N a q eta d e‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (8.2e-10 / sourceL N) :=
  norm_paper_retainedPacket_from_density hN hq haq hd (retainedCount_bulk_paid hN hq d e)
    (retainedCount_033_paid hN hq d e) hregion eta

theorem full_packet_numeric {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    ‖lowPacket N a q eta‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (0.0194 / sourceL N) :=
  norm_lowPacket_from_density hN hq haq (familyCount_bulk_paid hN hq)
    (familyCount_033_paid hN hq) h2 hregion eta

theorem paper_S_numeric {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        ((if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
          highPacket N a q eta)‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (8.2e-10 / sourceL N) :=
  paper_complete_error_from_density hN hi hq hd (retainedCount_bulk_paid hN hq d e)
    (retainedCount_033_paid hN hq d e) hregion eta

theorem full_S_numeric {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (0.0194 / sourceL N) :=
  complete_error_from_density hN hi hq (familyCount_bulk_paid hN hq)
    (familyCount_033_paid hN hq) h2 hregion eta

theorem r24_packet_numeric {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    ‖retainedPacket N a q eta d e‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (8.2e-10 / sourceL N) :=
  (norm_cutPacket_le (nat_pos_of_exp_le hN) haq eta _
    (fun _ => Finset.filter_subset _ _)).trans
    (mul_le_mul_of_nonneg_left (r24_retained_numeric hN hq hd hregion) (by positivity))

theorem r24_S_numeric {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : SourceAt (lowScale N) d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        ((if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
          highPacket N a q eta)‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (8.2e-10 / sourceL N) := by
  have he := complete_error_low_high hN hi hq eta
  rw [lowPacket_split_source hN hq hd] at he
  have hp := r24_packet_numeric hN hq hi.2.2 hd hregion eta
  have h := (norm_sub_le
    (S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
      ((retainedPacket N a q eta d e +
        if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
          highPacket N a q eta)) (retainedPacket N a q eta d e)).trans (add_le_add he hp)
  convert h using 1
  congr 1
  ring

end LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery
