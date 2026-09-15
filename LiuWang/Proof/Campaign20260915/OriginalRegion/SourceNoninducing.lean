import LiuWang.Proof.Campaign20260915.OriginalRegion.LowWeight

/-! The fixed real source also excludes high seeds at noninducing moduli
throughout the larger low window. No source-free classification is asserted.
-/

set_option autoImplicit false
noncomputable section

open Complex
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.Exception LiuWang.Proof.SourceRoute.Exception.Restart
open LiuWang.Proof.SourceRoute.LowSum
open LiuWang.Proof.SourceRoute.LowSum.Continuation.Restart
open LiuWang.Proof.SourceRoute.MajorOrdinary
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.OriginalRegion

theorem two_zero_scaled_budget_contradiction {x beta gamma : ℝ} (hx : 10 ≤ x)
    (hb1 : beta < 1) (hg1 : gamma < 1)
    (hb : (1 - beta) * Real.log x ≤ 1 / 8)
    (hg : (1 - gamma) * Real.log x ≤ 1 / 8)
    (hcore : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 23 / 20 →
      1 / (sigma - beta) + 1 / (sigma - gamma) ≤
        1 / (sigma - 1) + 4 * stechkinConductorCoeff * Real.log x) : False := by
  have hL := log_scale_ge hx
  have hL0 : 0 < Real.log x := by linarith
  let u := (3 / 10) / Real.log x
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 3 / 20 := by
    dsimp [u]
    apply (div_le_iff₀ hL0).mpr
    linarith
  have huL : u * Real.log x = 3 / 10 := by dsimp [u]; field_simp
  have hh := hcore (1 + u) (by linarith) (by linarith)
  have hinv : 1 / (1 + u - 1) = (10 / 3) * Real.log x := by
    dsimp [u]; field_simp; ring
  rw [hinv] at hh
  have hterm (b : ℝ) (hb1 : b < 1) (hgap : (1 - b) * Real.log x ≤ 1 / 8) :
      (40 / 17) * Real.log x ≤ 1 / (1 + u - b) := by
    apply (le_div_iff₀ (show 0 < 1 + u - b by linarith)).mpr
    nlinarith only [hgap, huL]
  have h1 := hterm beta hb1 hb
  have h2 := hterm gamma hg1 hg
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  nlinarith only [hh, h1, h2, hk, hL0]

theorem noninducing_low_window_absence {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : ¬d.modulus ∣ q) (chi : Character q) {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    rho.re < paperCap N := by
  by_contra hn
  have hp : paperCap N ≤ rho.re := le_of_not_gt hn
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  obtain ⟨hx, hqx, hy⟩ := low_scale_table_domain hN hq
  have hdx := (low_scale_table_domain (q := d.modulus) hN hd.1).2.1
  have hL := log_scale_ge (show 10 ≤ lowScale N by linarith)
  have hL0 : 0 < Real.log (lowScale N) := by linarith
  have hbscaled := original_seed_low_lambda hN hd.2.2.2.2.le
  have hrscaled := original_seed_low_lambda hN hp
  have hrhalf : 1 / 2 < rho.re := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_right h hL0.le
    nlinarith only [hh, hrscaled, hL]
  have hm := CompleteExpansion.mem_zeroValues.mp hr
  have hheight : |rho.im| ≤ lowScale N / q := by
    simpa only [hy] using hm.2.2.2.1
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  have hze : datumL d (e.re : ℂ) = 0 := by rw [he]; exact hd.2.1
  apply two_zero_scaled_budget_contradiction (show 10 ≤ lowScale N by linarith)
    hd.2.2.2.1 hm.2.2.1 (hbscaled.trans (by norm_num)) (hrscaled.trans (by norm_num))
  intro sigma hs hs1
  have hld := Real.log_le_log (Nat.cast_pos.mpr d.modulus_pos) hdx
  by_cases hc : chi = 1
  · have hrne : rho ≠ 1 := by
      intro heq
      have hh := hm.2.2.1
      rw [heq] at hh
      norm_num at hh
    have hzeta := (PrincipalPsi.principal_zero_iff_zeta_zero hm.2.1 hrne).mp
      (by simpa only [hc] using hm.1)
    obtain ⟨p, hv⟩ := exists_xi_index_of_zeta_zero hm.2.1 hzeta
    have hh := source_zeta_damped_bound d (paper_source_half hN hd) hze p
      (by simpa only [hv] using hrhalf) hs hs1
    rw [hv] at hh
    have ht1 := xi_zero_height_gt_one p
    rw [hv] at ht1
    have hqt := conductor_height_log_max_le hqx hheight
    rw [max_eq_right ht1.le] at hqt
    have hlt : Real.log |rho.im| ≤ Real.log (lowScale N) := by
      linarith [Real.log_natCast_nonneg q]
    have hlogs := mul_le_mul_of_nonneg_left (add_le_add hld hlt)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
    nlinarith only [hh, hlogs]
  · let : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hpr := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hc
    have hrd : (chi.conductor : ℝ) ≤ q := by
      exact_mod_cast BombieriVinogradov.DirichletCharacter.conductor_le_level chi
    have ht : |rho.im| ≤ lowScale N / chi.conductor :=
      hheight.trans (div_le_div_of_nonneg_left (by linarith)
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero chi.conductor_ne_zero)) hrd)
    have hpair : pairCharacter d.character chi.primitiveCharacter ≠ 1 := by
      intro hh
      exact hdiv ((pair_principal_forces_induction d chi.primitiveCharacter hh).1.trans
        chi.conductor_dvd_level)
    have hinverse : pairCharacter d.character chi.primitiveCharacter⁻¹ ≠ 1 := by
      intro hh
      exact hdiv ((pair_principal_forces_induction d chi.primitiveCharacter⁻¹ hh).1.trans
        chi.conductor_dvd_level)
    have hh := mixed_sources_damped_bound d chi.primitiveCharacter hpr
      chi.primitiveCharacter_isPrimitive hpair hinverse (paper_source_half hN hd)
      hrhalf hze (primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hc hm.2.1 hm.1)
      hs hs1
    have hqt := conductor_height_log_max_le (hrd.trans hqx) ht
    have hlogs := mul_le_mul_of_nonneg_left (add_le_add hld hqt)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) conductorCoeff_bounds.1)
    nlinarith only [hh, hlogs]

theorem low_zero_iff_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (chi : Character q) {rho : ℂ} :
    (rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q) ∧ paperCap N ≤ rho.re) ↔
      d.modulus ∣ q ∧ chi = inducedAt d q ∧ rho = e := by
  constructor
  · rintro ⟨hr, hp⟩
    have hdiv : d.modulus ∣ q := by
      by_contra hh
      exact (not_lt_of_ge hp) (noninducing_low_window_absence hN hq hd hh chi hr)
    have hcap : cap N 0.3221 ≤ paperCap N :=
      (cap_order hN (by norm_num : (0.11 : ℝ) ≤ 0.3221)).trans (cap_011_le_paper hN)
    have hnotret : ¬(chi ≠ inducedAt d q ∨ rho ≠ e) := by
      intro hret
      exact (not_lt_of_ge (hcap.trans hp))
        (paper_source_retained_strict hN hq hd hdiv chi (Finset.mem_filter.mpr ⟨hr, hret⟩))
    exact ⟨hdiv, by tauto⟩
  · intro hh
    obtain ⟨hr, _, hp⟩ := (short_zero_iff_source hN hq hd chi).mpr hh
    exact ⟨hr, hp⟩

theorem paper_source_nonreal_seed_cap {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q))
    (hp : paperCap N ≤ rho.re) (hi : rho.im ≠ 0) :
    rho.re ≤ cap N (1 / 9.645908801) := by
  have he := ((low_zero_iff_source hN hq hd chi).mp ⟨hr, hp⟩).2.2
  exact False.elim (hi (by rw [he]; exact hd.2.2.1))

theorem lowWeightSum_noninducing_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : ¬d.modulus ∣ q) :
    lowWeightSum N q ≤ 0.0194 / sourceL N := by
  rw [lowWeightSum_eq_lowSum hN]
  exact original_low_sum_of_short_absence hN hq
    (short_absence_of_not_dvd hN hq hd hdiv)
    (fun _ _ hr hp hi => paper_source_nonreal_seed_cap hN hq hd hr hp hi)

theorem lowWeightSum_paper_source_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    lowWeightSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤
      0.0194 / sourceL N := by
  by_cases hdiv : d.modulus ∣ q
  · rw [if_pos hdiv]
    exact (lowWeightSum_induced_primed_bound hN hq hd hdiv).trans
      (div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN]))
  · rw [if_neg hdiv, sub_zero]
    exact lowWeightSum_noninducing_bound hN hq hd hdiv

end LiuWang.Proof.Campaign20260915.OriginalRegion
