import LiuWang.Proof.Campaign20260915.SecondTerminal.RegionPaid

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CompleteExpansion LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.WeightedLowZeros LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.SourceRoute.LowSum
open LiuWang.Proof.SourceRoute.SecondArc.Continuation

namespace LiuWang.Proof.Campaign20260915.SecondTerminal

theorem original_sqrt_totient_le (q : ℕ) [NeZero q] :
    Real.sqrt q / q.totient ≤ Real.sqrt 2 := by
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  apply (div_le_iff₀ hp).mpr
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact_mod_cast SingularSeries.le_two_mul_totient_sq q

theorem inducing_source_of_real_low_zero {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {chi : Character q} {rho : ℂ}
    (hr : rho ∈ zeroValues chi (omegaCutoff N q)) (hi : rho.im = 0)
    (hb : paperCap N < rho.re) :
    ∃ d : PrimitiveQuadraticDatum, PaperSource N d rho ∧ d.modulus ∣ q := by
  have hm := mem_zeroValues.mp hr
  have hx := OriginalRegion.sourceP_original_scale hN
  have hc := OriginalRegion.source_free_original_classification hx hq chi hb hm.2.2.1
    (by rw [hi, abs_zero]; positivity) hm.1
  have he : (rho.re : ℂ) = rho := by apply Complex.ext <;> simp [hi]
  obtain ⟨d, hd, _, hdq, _, hz, _, _⟩ :=
    ZeroRegionFamily.ApplicationScale.Continuation.Frontier.real_family_fixed_source_original
      (beta := rho.re) (by linarith : 10 ≤ sourceP N) hq chi hc.1 hc.2.1
      (by change 1 - 1 / (9.645908801 * Real.log (sourceP N)) < rho.re at hb; linarith)
      (by simpa only [he] using hm.1)
  exact ⟨d, ⟨hd, by simpa only [he] using hz, hi, hm.2.2.1, hb⟩, hdq⟩

theorem low_cap_of_no_inducing_source {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hno : ¬∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e ∧ d.modulus ∣ q) :
    ∀ chi : Character q, ∀ rho ∈ zeroValues chi (omegaCutoff N q),
      paperCap N ≤ rho.re → rho.re ≤ cap N (1 / 9.645908801) := by
  have hP := sourceP_pos (exp_2000_le_of_exp_3100_le hN)
  have hlog : 0 < Real.log (sourceP N) := Real.log_pos
    (lt_of_lt_of_le (by norm_num) (OriginalRegion.sourceP_original_scale hN))
  have hPlow : sourceP N ≤ lowScale N := by change sourceP N ≤ 3.36 * sourceP N; linarith
  have hl := Real.log_le_log hP hPlow
  have hc : paperCap N ≤ cap N (1 / 9.645908801) := by
    have hh := one_div_le_one_div_of_le
      (show 0 < 9.645908801 * Real.log (sourceP N) by positivity)
      (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 9.645908801))
    simpa only [paperCap, cap, div_div] using sub_le_sub_left hh 1
  intro chi rho hr _
  by_contra hn
  have hb := lt_of_not_ge hn
  have hi : rho.im = 0 := by
    by_contra hi
    exact (not_le_of_gt hb) (OriginalRegion.source_free_nonreal_seed_cap hN hq hr hi)
  obtain ⟨d, hd, hdq⟩ := inducing_source_of_real_low_zero hN hq hr hi (hc.trans_lt hb)
  exact hno ⟨d, rho, hd, hdq⟩

theorem original_low_packet_le_closed_mass {N q a : ℕ} [NeZero q] (eta : ℝ) :
    ‖originalLowPacket N q a eta‖ ≤ (q.totient : ℝ)⁻¹ *
      ∑ chi : Character q, ‖G a chi‖ *
        ∑ rho ∈ zeroValues chi (omegaCutoff N q),
          (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖ := by
  rw [originalLowPacket, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro chi _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, Complex.norm_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    obtain ⟨hr, hh⟩ := Finset.mem_filter.mp hr
    have hm := mem_zeroValues.mp hr
    exact mem_zeroValues.mpr ⟨hm.1, hm.2.1, hm.2.2.1, hh.le, hm.2.2.2.2⟩
  · intros
    positivity

theorem original_low_packet_absence {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ)
    (hno : ¬∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e ∧ d.modulus ∣ q) :
    ‖originalLowPacket N q a eta‖ ≤ 0.0194 * Real.sqrt 2 * (N : ℝ) / sourceL N := by
  have hs := SourceRoute.LowSum.Continuation.Restart.original_full_Jrho_bound hN hq
    (low_cap_of_no_inducing_source hN hq hno) eta
  have hg (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt q :=
    (norm_G_le_sqrt_conductor ha chi).trans (Real.sqrt_le_sqrt
      (Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)))
  have hm : (∑ chi : Character q, ‖G a chi‖ *
      ∑ rho ∈ zeroValues chi (omegaCutoff N q),
        (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
      Real.sqrt q * ((N : ℝ) * (0.0194 / sourceL N)) := by
    calc
      _ ≤ ∑ chi : Character q, Real.sqrt q *
          ∑ rho ∈ zeroValues chi (omegaCutoff N q),
            (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖ :=
        Finset.sum_le_sum fun chi _ => mul_le_mul_of_nonneg_right (hg chi) (by positivity)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hp := (original_low_packet_le_closed_mass (N := N) (q := q) (a := a) eta).trans
    (mul_le_mul_of_nonneg_left hm (by positivity))
  have hh := mul_le_mul_of_nonneg_right (original_sqrt_totient_le q)
    (show 0 ≤ (N : ℝ) * (0.0194 / sourceL N) by
      have := sourceL_ge_3100 hN; positivity)
  simp only [div_eq_mul_inv] at hp hh ⊢
  nlinarith only [hp, hh]

theorem original_exceptional_payment {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : deltaRadius N q < |eta|)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    (q.totient : ℝ)⁻¹ * (‖G a (inducedAt d q)‖ * ‖Jrho N e eta‖) ≤
      (10 * (N : ℝ) / (3.36 * Real.sqrt (sourceP N))) * sourceNu (sourceP N) := by
  have hN0 := exp_2000_le_of_exp_3100_le hN
  have hP := sourceP_pos hN0
  have hdelta := deltaRadius_pos hN0 (NeZero.pos q)
  have he : eta ≠ 0 := abs_pos.mp (hdelta.trans heta)
  have hw : (0.001 * (N : ℝ)) ^ (e.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [source_endpoint_ge_thousand hN])
      (by linarith [hd.2.2.2.1])
  have hj := (OscillatoryBounds.Jrho_real_reciprocal (nat_pos_of_exp_le hN)
    hd.2.2.2.1.le hd.2.2.1 he).trans
      (div_le_div_of_nonneg_right hw (by positivity))
  have hJ := hj.trans (one_div_le_one_div_of_le (mul_pos Real.pi_pos hdelta)
    (mul_le_mul_of_nonneg_left heta.le Real.pi_pos.le))
  have hG : ‖G a (inducedAt d q)‖ ≤ Real.sqrt (sourceP N) :=
    (norm_G_le_sqrt_conductor ha _).trans (Real.sqrt_le_sqrt
      ((Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level _)).trans hq))
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul hG hJ (norm_nonneg _) (by positivity)) (show 0 ≤ (q.totient : ℝ)⁻¹ by positivity)
  have heq : (q.totient : ℝ)⁻¹ * (Real.sqrt (sourceP N) *
      (1 / (Real.pi * deltaRadius N q))) =
      (10 * (N : ℝ) / (3.36 * Real.sqrt (sourceP N))) * ((q : ℝ) / q.totient) := by
    unfold deltaRadius
    have hs := Real.sqrt_pos.mpr hP
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hn := natCast_pos_of_exp_le hN
    field_simp
    rw [Real.sq_sqrt hP.le]
  rw [heq] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hnu (by positivity))

theorem original_low_packet_inducing {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : deltaRadius N q < |eta|)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖originalLowPacket N q a eta‖ ≤
      (10 * (N : ℝ) / (3.36 * Real.sqrt (sourceP N))) * sourceNu (sourceP N) +
      8.2e-10 * Real.sqrt 2 * (N : ℝ) / sourceL N := by
  have hL : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have hg (chi : Character q) : ‖G a chi‖ ≤ Real.sqrt q :=
    (norm_G_le_sqrt_conductor ha chi).trans (Real.sqrt_le_sqrt
      (Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)))
  have hs := sum_split_retained (q := q) (omegaCutoff N q) d e
    (fun chi rho => ‖G a chi‖ * ((zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖))
  simp only [paper_induced_mem_iff hN hq hd, if_pos hdiv,
    paper_source_multiplicity hN hd hdiv, Nat.cast_one, one_mul] at hs
  have hr : (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      ‖G a chi‖ * ((zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖)) ≤
      Real.sqrt q * ((N : ℝ) * (8.2e-10 / sourceL N)) := by
    calc
      _ ≤ ∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
          Real.sqrt q * ((zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) :=
        Finset.sum_le_sum fun chi _ => Finset.sum_le_sum fun rho _ =>
          mul_le_mul_of_nonneg_right (hg chi) (by positivity)
      _ ≤ _ := by
        simp only [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (SourceRoute.LowSum.Continuation.induced_retained_Jrho_bound hN hq hd hdiv eta)
          (by positivity)
  have hp := original_low_packet_le_closed_mass (N := N) (q := q) (a := a) eta
  simp only [← Finset.mul_sum] at hs
  rw [hs, mul_add] at hp
  have hrp := mul_le_mul_of_nonneg_left hr (show 0 ≤ (q.totient : ℝ)⁻¹ by positivity)
  have hsq := mul_le_mul_of_nonneg_right (original_sqrt_totient_le q)
    (show 0 ≤ (N : ℝ) * (8.2e-10 / sourceL N) by positivity)
  have hep := original_exceptional_payment hN hq ha heta hd hnu
  simp only [div_eq_mul_inv, Finset.mul_sum] at hp hrp hsq hep ⊢
  nlinarith only [hp, hrp, hsq, hep]

theorem original_low_packet_cases {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) {eta : ℝ} (heta : deltaRadius N q < |eta|)
    (hnu : (q : ℝ) / q.totient ≤ sourceNu (sourceP N)) :
    ‖originalLowPacket N q a eta‖ ≤
      max (0.0194 * Real.sqrt 2 * (N : ℝ) / sourceL N)
        ((10 * (N : ℝ) / (3.36 * Real.sqrt (sourceP N))) * sourceNu (sourceP N) +
          8.2e-10 * Real.sqrt 2 * (N : ℝ) / sourceL N) := by
  by_cases hex : ∃ (d : PrimitiveQuadraticDatum) (e : ℂ), PaperSource N d e ∧ d.modulus ∣ q
  · obtain ⟨d, e, hd, hdiv⟩ := hex
    exact (original_low_packet_inducing hN hq ha heta hd hdiv hnu).trans (le_max_right _ _)
  · exact (original_low_packet_absence hN hq ha eta hex).trans (le_max_left _ _)

#print axioms original_low_packet_cases

end LiuWang.Proof.Campaign20260915.SecondTerminal
