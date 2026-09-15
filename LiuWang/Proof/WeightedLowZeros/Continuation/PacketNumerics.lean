import LiuWang.Proof.WeightedLowZeros.Continuation.PaperSource
import LiuWang.Proof.WeightedLowZeros.Consumer

/-!
# Conditional numerical payments in the original complete-S expansion

The high-height packet and the complete expansion error are unchanged. Near-one
counts and pointwise regions remain explicit inputs, never weighted-sum inputs.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.ZeroRegionFamily
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

theorem norm_cutPacket_le {N a q : ℕ} [NeZero q] (hN : 0 < N)
    (haq : Nat.Coprime a q) (eta : ℝ) (Z : Character q → Finset ℂ)
    (hZ : ∀ chi, Z chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    ‖(q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
        ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * cutMass N q Z := by
  have hG (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt (q : ℝ) :=
    (norm_G_le_sqrt_conductor haq chi).trans
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr
        (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level)))
  have hc (chi : Character q) :
      ‖G a chi * ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta‖ ≤
        Real.sqrt (q : ℝ) *
          ((N : ℝ) * ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℝ) * weight N rho.re) := by
    rw [norm_mul]
    exact mul_le_mul (hG chi)
      (norm_subset_Jrho_le hN chi (omegaCutoff N q) eta (Z chi) (hZ chi))
      (norm_nonneg _) (Real.sqrt_nonneg _)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q,
        Real.sqrt (q : ℝ) *
          ((N : ℝ) * ∑ rho ∈ Z chi, (zeroMultiplicity chi rho : ℝ) * weight N rho.re) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun chi _ => hc chi))
        (by positivity)
    _ = _ := by simp only [cutMass, ← Finset.mul_sum, mul_assoc]

theorem norm_lowPacket_from_density {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (haq : Nat.Coprime a q)
    (h14000 : familyCount q (bulkCap N) (omegaCutoff N q) ≤ 14000)
    (h13 : familyCount q (cap N 0.33) (omegaCutoff N q) ≤ 13)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    ‖lowPacket N a q eta‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (0.0194 / sourceL N) := by
  have h := norm_cutPacket_le (nat_pos_of_exp_le hN) haq eta
    (fun chi => CompleteExpansion.zeroValues chi (omegaCutoff N q)) (fun _ _ hr => hr)
  change ‖lowPacket N a q eta‖ ≤
    ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * lowSum N q at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (nonexceptional_density_budget hN hq h14000 h13 h2 hregion) (by positivity))

theorem paper_lowPacket_split {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) (eta : ℝ) :
    lowPacket N a q eta = retainedPacket N a q eta d e +
      if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0 := by
  have h := sum_split_retained (q := q) (omegaCutoff N q) d e
    (fun chi rho => G a chi * ((zeroMultiplicity chi rho : ℂ) * Jrho N rho eta))
  simp only [paper_induced_mem_iff hN hq hd, ← Finset.mul_sum] at h
  have hh := congrArg (fun z : ℂ => (q.totient : ℂ)⁻¹ * z) h
  by_cases hdq : d.modulus ∣ q
  · simpa only [lowPacket, retainedPacket, CompleteExpansion.zeroValueSum, zeroMultiplicity,
      if_pos hdq, show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from
        paper_source_multiplicity hN hd hdq, Nat.cast_one, one_mul, mul_add, mul_assoc] using hh
  · simpa only [lowPacket, retainedPacket, CompleteExpansion.zeroValueSum, zeroMultiplicity,
      if_neg hdq, add_zero] using hh

theorem norm_paper_retainedPacket_from_density {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (haq : Nat.Coprime a q)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h14000 : retainedCount q (bulkCap N) (omegaCutoff N q) d e ≤ 14000)
    (h13 : retainedCount q (cap N 0.33) (omegaCutoff N q) d e ≤ 13)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    ‖retainedPacket N a q eta d e‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (8.2e-10 / sourceL N) := by
  have hw := paper_source_numeric_from_density hN hq hd h14000 h13 hregion
  rw [paper_source_low_split hN hq hd, add_sub_cancel_right] at hw
  have h := norm_cutPacket_le (nat_pos_of_exp_le hN) haq eta
    (fun chi => retainedValues chi (omegaCutoff N q) d e) (fun _ => Finset.filter_subset _ _)
  change ‖retainedPacket N a q eta d e‖ ≤
    ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) *
      retainedSum N q (omegaCutoff N q) d e at h
  exact h.trans (mul_le_mul_of_nonneg_left hw (by positivity))

theorem complete_error_from_density {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    (h14000 : familyCount q (bulkCap N) (omegaCutoff N q) ≤ 14000)
    (h13 : familyCount q (cap N 0.33) (omegaCutoff N q) ≤ 13)
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (0.0194 / sourceL N) := by
  have he := complete_error_low_high hN hi hq eta
  have hp := norm_lowPacket_from_density hN hq hi.2.2 h14000 h13 h2 hregion eta
  have hid :
      S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta =
      (S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        (lowPacket N a q eta + highPacket N a q eta)) - lowPacket N a q eta := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add he hp)

theorem paper_complete_error_from_density {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h14000 : retainedCount q (bulkCap N) (omegaCutoff N q) d e ≤ 14000)
    (h13 : retainedCount q (cap N 0.33) (omegaCutoff N q) d e ≤ 13)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        ((if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
          highPacket N a q eta)‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (8.2e-10 / sourceL N) := by
  have he := complete_error_low_high hN hi hq eta
  rw [paper_lowPacket_split hN hq hd] at he
  have hp := norm_paper_retainedPacket_from_density hN hq hi.2.2 hd h14000 h13 hregion eta
  have hid :
      S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        ((if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
          highPacket N a q eta) =
      (S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        ((retainedPacket N a q eta d e +
          if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
            highPacket N a q eta)) - retainedPacket N a q eta d e := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add he hp)

end LiuWang.Proof.WeightedLowZeros.Continuation
