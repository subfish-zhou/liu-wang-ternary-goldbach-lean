import LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery.ExtendedWeight

/-!
# Smaller unpaid tails, with the original numerical targets and normalization

The pointwise retained cap and the full-family two-zero input now concern
lambda .27 rather than .3221. Neither of those remaining inputs is asserted.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.CharacterExpansion
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery

theorem cap_antitone {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a b : ℝ} (hab : a ≤ b) : cap N b ≤ cap N a := by
  have hl : 25 ≤ Real.log (lowScale N) := (log_scale_bounds (sourceL_ge_3100 hN)).1
  have hlog : 0 < Real.log (lowScale N) := by linarith
  exact sub_le_sub_left (div_le_div_of_nonneg_right hab hlog.le) 1

theorem cap_half {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {c : ℝ} (hc : c ≤ 0.478) : 1/2 ≤ cap N c := by
  have hlog : 25 ≤ Real.log (lowScale N) := (log_scale_bounds (sourceL_ge_3100 hN)).1
  have hdiv : c / Real.log (lowScale N) ≤ 1/2 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  dsimp [cap]
  linarith

theorem two_027_of_two_03221 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    (h2 : familyCount q (cap N 0.3221) (omegaCutoff N q) ≤ 2) :
    familyCount q (cap N 0.27) (omegaCutoff N q) ≤ 2 :=
  (NearOneDensity.Continuation.familyCount_antitone_alpha
    (cap_antitone hN (by norm_num : (0.27 : ℝ) ≤ 0.3221))).trans h2

theorem retained_numeric_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) :
    retainedSum N q (omegaCutoff N q) d e ≤ 7.6e-10 / sourceL N :=
  cutMass_to_027 hN hq _ (fun _ => Finset.filter_subset _ _) hregion

theorem paper_numeric_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) :
    lowSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 7.6e-10 / sourceL N := by
  rw [paper_source_low_split hN hq hd, add_sub_cancel_right]
  exact retained_numeric_027 hN hq d e hregion

theorem full_numeric_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : familyCount q (cap N 0.27) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N := by
  let Z := fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q)
  let B := fun chi => (Z chi).filter (fun rho => cap N 0.27 < rho.re)
  have hB : ∀ chi, B chi ⊆ CompleteExpansion.zeroValues chi (omegaCutoff N q) :=
    fun _ => Finset.filter_subset _ _
  have hc : cutCount q B (cap N 0.27) ≤ 2 := by
    apply (cutCount_mono B Z hB _).trans
    simpa only [cutCount, Z, familyCount, count,
      Applications.values_eq_complete_filter _ (cap_half hN (by norm_num : (0.27 : ℝ) ≤ 0.478)),
      zeroMultiplicity] using h2
  have hm := cutMass_le_count (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (cap N 0.27) (cap_positive hN (by norm_num : (1/9.645908801 : ℝ) ≤ 0.478)) B hB
    (fun _ _ hr => (Finset.mem_filter.mp hr).2.le)
    (fun chi rho hr => hregion chi rho (hB chi hr))
  have hp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hw := mul_le_mul (weight_source_c1_payment hN) (Nat.cast_le.mpr hc : (_ : ℝ) ≤ 2)
    (Nat.cast_nonneg _) (by positivity)
  change cutMass N q Z ≤ _
  rw [cutMass_partition N q Z (cap N 0.27)]
  apply (add_le_add (actual_bulk_to_027 hN hq) (hm.trans hw)).trans
  apply (le_div_iff₀ hp).mpr
  field_simp
  norm_num

theorem retained_Jrho_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤ (N : ℝ) * (7.6e-10 / sourceL N) :=
  (cut_Jrho_le (nat_pos_of_exp_le hN) _ (fun _ => Finset.filter_subset _ _) eta).trans
    (mul_le_mul_of_nonneg_left (retained_numeric_027 hN hq d e hregion) (Nat.cast_nonneg _))

theorem retained_packet_027 {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) (eta : ℝ) :
    ‖retainedPacket N a q eta d e‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (7.6e-10 / sourceL N) :=
  (norm_cutPacket_le (nat_pos_of_exp_le hN) haq eta _
    (fun _ => Finset.filter_subset _ _)).trans
    (mul_le_mul_of_nonneg_left (retained_numeric_027 hN hq d e hregion) (by positivity))

theorem full_Jrho_027 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : familyCount q (cap N 0.27) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤ (N : ℝ) * (0.0194 / sourceL N) :=
  (cut_Jrho_le (nat_pos_of_exp_le hN) _ (fun _ _ hr => hr) eta).trans
    (mul_le_mul_of_nonneg_left (full_numeric_027 hN hq h2 hregion) (Nat.cast_nonneg _))

theorem full_packet_027 {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (haq : Nat.Coprime a q)
    (h2 : familyCount q (cap N 0.27) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    ‖lowPacket N a q eta‖ ≤
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (0.0194 / sourceL N) :=
  (norm_cutPacket_le (nat_pos_of_exp_le hN) haq eta _ (fun _ _ hr => hr)).trans
    (mul_le_mul_of_nonneg_left (full_numeric_027 hN hq h2 hregion) (by positivity))

theorem full_S_027 {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    (h2 : familyCount q (cap N 0.27) (omegaCutoff N q) ≤ 2)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) →
        rho.re ≤ cap N (1/9.645908801)) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (0.0194 / sourceL N) := by
  have he := complete_error_low_high hN hi hq eta
  have hp := full_packet_027 hN hq hi.2.2 h2 hregion eta
  have hid :
      S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        highPacket N a q eta =
      (S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        (lowPacket N a q eta + highPacket N a q eta)) - lowPacket N a q eta := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add he hp)

theorem paper_S_027 {N a q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.27) (eta : ℝ) :
    ‖S N (rationalCenter a q + eta) - CompleteExpansion.principalCoefficient q * J N eta +
        ((if d.modulus ∣ q then (q.totient : ℂ)⁻¹ * G a (inducedAt d q) * Jrho N e eta else 0) +
          highPacket N a q eta)‖ ≤ CompleteExpansion.errorBound q N a eta +
      ((q.totient : ℝ)⁻¹ * (Real.sqrt (q : ℝ) * (N : ℝ))) * (7.6e-10 / sourceL N) := by
  have he := complete_error_low_high hN hi hq eta
  rw [paper_lowPacket_split hN hq hd] at he
  have hp := retained_packet_027 hN hq hi.2.2 d e hregion eta
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

end LiuWang.Proof.WeightedLowZeros.Continuation.DensityRecovery
