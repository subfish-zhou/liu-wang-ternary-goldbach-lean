import LiuWang.Proof.Campaign20260915.OriginalRegion.SourceNoninducing

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.Exception LiuWang.Proof.SourceRoute.Exception.Restart
open LiuWang.Proof.SourceRoute.LowSum LiuWang.Proof.SourceRoute.LowSum.Continuation
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaMultiplicativeTransfer
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ChebyshevBound.HighHeight

namespace LiuWang.Proof.Campaign20260915.MajorArc

theorem asymmetric_two_zero_contradiction {x beta gamma : ℝ} (hx : 10 ≤ x)
    (hb1 : beta < 1) (hg1 : gamma < 1)
    (hb : (1 - beta) * Real.log x ≤ 0.11)
    (hg : (1 - gamma) * Real.log x ≤ 0.19)
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
  have h1 : (100 / 41) * Real.log x ≤ 1 / (1 + u - beta) := by
    apply (le_div_iff₀ (show 0 < 1 + u - beta by linarith)).mpr
    nlinarith only [hb, huL]
  have h2 : (100 / 49) * Real.log x ≤ 1 / (1 + u - gamma) := by
    apply (le_div_iff₀ (show 0 < 1 + u - gamma by linarith)).mpr
    nlinarith only [hg, huL]
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_bounds.2 hL0.le
  nlinarith only [hh, h1, h2, hk, hL0]

theorem noninducing_cap_019 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : ¬d.modulus ∣ q) (chi : Character q) {rho : ℂ}
    (hr : rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q)) :
    rho.re < cap N 0.19 := by
  by_contra hn
  have hp : cap N 0.19 ≤ rho.re := le_of_not_gt hn
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  obtain ⟨hx, hqx, hy⟩ := low_scale_table_domain hN hq
  have hdx := (low_scale_table_domain (q := d.modulus) hN hd.1).2.1
  have hL := log_scale_ge (show 10 ≤ lowScale N by linarith)
  have hL0 : 0 < Real.log (lowScale N) := by linarith
  have hbscaled := original_seed_low_lambda hN hd.2.2.2.2.le
  have hrscaled : (1 - rho.re) * Real.log (lowScale N) ≤ 0.19 := by
    have hh : 1 - rho.re ≤ 0.19 / Real.log (lowScale N) := by
      dsimp [cap] at hp
      linarith
    exact (le_div_iff₀ hL0).mp hh
  have hrhalf : 1 / 2 < rho.re := by
    linarith [cap_ge_098 hN (by norm_num : (0.19 : ℝ) ≤ 0.478)]
  have hm := CompleteExpansion.mem_zeroValues.mp hr
  have hheight : |rho.im| ≤ lowScale N / q := by
    simpa only [hy] using hm.2.2.2.1
  have he : (e.re : ℂ) = e := by
    apply Complex.ext <;> simp [hd.2.2.1]
  have hze : datumL d (e.re : ℂ) = 0 := by rw [he]; exact hd.2.1
  apply asymmetric_two_zero_contradiction (show 10 ≤ lowScale N by linarith)
    hd.2.2.2.1 hm.2.2.1 hbscaled hrscaled
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

theorem seed_019_upper : seedExp 0.19 ≤ 1e-10 := by
  have h : 1e-11 ≤ seedExp 0.19 ∧ seedExp 0.19 ≤ 1e-10 := by
    apply seed_enclosure (n := 23) (xl := 0.2) (xu := 0.3) <;>
      norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]
  exact h.2

theorem retained_tail_019 {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (d : PrimitiveQuadraticDatum) (e : ℂ)
    (hcap : ∀ chi : Character q, ∀ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      rho.re ≤ cap N 0.19) :
    (∫ alpha in bulkCap N..1,
      kernel N alpha * (retainedCount q alpha (omegaCutoff N q) d e : ℝ)) ≤
        0.0000042 / sourceL N := by
  let Z := fun chi : Character q => retainedValues chi (omegaCutoff N q) d e
  have hab := cap_order hN (by norm_num : (0.19 : ℝ) ≤ 0.33)
  have hbc := cap_le_one hN (by norm_num : (0 : ℝ) ≤ 0.19)
  have ha : 0 < cap N 0.33 := by linarith [cap_ge_098 hN (by norm_num : (0.33 : ℝ) ≤ 0.478)]
  have hfirst := subset_first_eight_paid hN hq Z (fun _ => Finset.filter_subset _ _)
  have hcount : countingFunction Z zeroMultiplicity (cap N 0.33) ≤ 13 := by
    simpa only [breakpoint, rowCount, Nat.cast_ofNat] using
      subset_nine_rows hN hq Z (fun _ => Finset.filter_subset _ _) (i := 8) (by norm_num)
  have hmid := counting_integral_le_open (nat_pos_of_exp_le hN) Z zeroMultiplicity ha hab
    (fun _ halpha => (countingFunction_antitone Z zeroMultiplicity halpha.1.le).trans hcount)
  have hpaid : (∫ alpha in cap N 0.33..cap N 0.19, 13 * kernel N alpha) ≤
      0.00000419 / sourceL N := by
    apply segment_paid hN seed_019_upper seed_033.1 <;> norm_num
  have hz := counting_integral_zero_above_cap N Z zeroMultiplicity hbc hcap
  have he := intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable (nat_pos_of_exp_le hN) ha hab Z zeroMultiplicity)
    (counting_integrand_integrable (nat_pos_of_exp_le hN) (ha.trans_le hab) hbc Z zeroMultiplicity)
  have he' := intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable (nat_pos_of_exp_le hN)
      (by linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)])
      (cap_order hN (by norm_num : (0.33 : ℝ) ≤ 0.478)) Z zeroMultiplicity)
    (counting_integrand_integrable (nat_pos_of_exp_le hN) ha (hab.trans hbc) Z zeroMultiplicity)
  simp only [Z, countingFunction_retained] at hfirst hmid hz he he'
  change (∫ alpha in cap N 0.478..1, _) ≤ _
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  have hsum : (3e-13 : ℝ) / sourceL N + 0.00000419 / sourceL N ≤
      0.0000042 / sourceL N := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hL.le
  linarith [hmid.trans hpaid]

theorem retained_low_all_moduli {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    retainedSum N q (omegaCutoff N q) d e ≤ 0.000005 / sourceL N := by
  have hL := sourceL_pos (exp_2000_le_of_exp_3100_le hN)
  by_cases hdiv : d.modulus ∣ q
  · exact (induced_retained_weighted_bound hN hq hd hdiv).trans
      (div_le_div_of_nonneg_right (by norm_num) hL.le)
  · have ht := retained_tail_019 hN hq d e (fun chi rho hr =>
      (noninducing_cap_019 hN hq hd hdiv chi (Finset.mem_filter.mp hr).1).le)
    have hr := retained_original_reduction hN hq d e
    exact (hr.trans (add_le_add le_rfl ht)).trans (by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hL.le)

#print axioms retained_low_all_moduli

end LiuWang.Proof.Campaign20260915.MajorArc
