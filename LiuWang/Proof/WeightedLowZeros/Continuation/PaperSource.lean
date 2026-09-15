import LiuWang.Proof.WeightedLowZeros.Continuation.DensityNumerics

/-!
# A fixed actual source in the paper's c1 region, without an R24 identification

Existence and uniqueness of this wider source are not asserted. Given one fixed
actual primitive datum and zero, its ordinary multiplicity and exact deleted
term are paid, and the sufficient density branch has the original normalization.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ChebyshevBound.HighHeight
open AnalyticNumberTheory.LargeSieve

namespace LiuWang.Proof.WeightedLowZeros.Continuation

def PaperSource (N : ℕ) (d : PrimitiveQuadraticDatum) (e : ℂ) : Prop :=
  (d.modulus : ℝ) ≤ sourceP N ∧ datumL d e = 0 ∧ e.im = 0 ∧ e.re < 1 ∧
    1 - 1 / (9.645908801 * Real.log (sourceP N)) < e.re

theorem paper_source_half {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) : 1/2 < e.re := by
  have hlog := (low_parameter_logs (q := 1) hN
    (by simpa only [Nat.cast_one] using one_le_sourceP (exp_2000_le_of_exp_3100_le hN))).1
  have hgap : 1 / (9.645908801 * Real.log (sourceP N)) ≤ 1/2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith [hd.2.2.2.2]

theorem paper_induced_zero {N q : ℕ} [NeZero q]
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) : (inducedAt d q).LFunction e = 0 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  rw [inducedAt, dif_pos hdiv,
    DirichletCharacter.LFunction_changeLevel hdiv d.character (Or.inl d.ne_one)]
  change datumL d e * _ = 0
  rw [hd.2.1, zero_mul]

theorem paper_source_multiplicity {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ))
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (hdiv : d.modulus ∣ q) : zeroMultiplicity (inducedAt d q) e = 1 := by
  let : NeZero d.modulus := ⟨d.modulus_ne⟩
  have hc : inducedAt d q ≠ 1 := by
    rw [inducedAt, dif_pos hdiv]
    exact fun h => d.ne_one ((DirichletCharacter.changeLevel_eq_one_iff hdiv).mp h)
  have hcond : (inducedAt d q).conductor = d.modulus := by
    rw [inducedAt, dif_pos hdiv, DirichletCharacter.conductor_changeLevel, d.isPrimitive]
  have hdlog : 1 < Real.log d.modulus := by
    have h := log_level_gt_one
      (BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one d.character d.ne_one)
    rwa [d.isPrimitive] at h
  have hlog := Real.log_le_log (Nat.cast_pos.mpr d.modulus_pos) hd.1
  have hgap : 1 / (9.645908801 * Real.log (sourceP N)) ≤ 1 / (3 * Real.log d.modulus) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  apply real_zero_simple hc (by linarith [paper_source_half hN hd])
    (paper_induced_zero hd hdiv) hd.2.2.1
  rw [hcond]
  linarith [hd.2.2.2.2]

theorem paper_induced_mem_iff {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    e ∈ CompleteExpansion.zeroValues (inducedAt d q) (omegaCutoff N q) ↔ d.modulus ∣ q := by
  have hb := paper_source_half hN hd
  constructor
  · intro he
    by_contra hn
    have hm := CompleteExpansion.mem_zeroValues.mp he
    have hc : inducedAt d q = 1 := by simp only [inducedAt, dif_neg hn]
    rw [hc] at hm
    have hep : e ≠ 1 := fun h => by simp [h] at hm
    have hz := (PrincipalPsi.principal_zero_iff_zeta_zero hm.2.1 hep).mp hm.1
    obtain ⟨p, hp⟩ := exists_xi_index_of_zeta_zero hm.2.1 hz
    have hh := xi_zero_height_gt_one p
    rw [hp, hd.2.2.1, abs_zero] at hh
    linarith
  · intro hdiv
    have hy := omegaCutoff_ge (NeZero.pos q) hq
    exact CompleteExpansion.mem_zeroValues.mpr
      ⟨paper_induced_zero hd hdiv, by linarith, hd.2.2.2.1,
        by rw [hd.2.2.1, abs_zero]; linarith, hb.le⟩

theorem paper_source_low_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) :
    lowSum N q = retainedSum N q (omegaCutoff N q) d e +
      if d.modulus ∣ q then weight N e.re else 0 := by
  have h := sum_split_retained (q := q) (omegaCutoff N q) d e
    (fun chi rho => (zeroMultiplicity chi rho : ℝ) * weight N rho.re)
  simp only [paper_induced_mem_iff hN hq hd] at h
  by_cases hdiv : d.modulus ∣ q
  · simpa only [lowSum, weightedSum, retainedSum, if_pos hdiv,
      paper_source_multiplicity hN hd hdiv, Nat.cast_one, one_mul] using h
  · simpa only [lowSum, weightedSum, retainedSum, if_neg hdiv] using h

theorem paper_source_count_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    {alpha : ℝ} (ha : 1/2 ≤ alpha) :
    familyCount q alpha (omegaCutoff N q) = retainedCount q alpha (omegaCutoff N q) d e +
      if d.modulus ∣ q ∧ alpha ≤ e.re then 1 else 0 := by
  have h := sum_split_retained (q := q) (omegaCutoff N q) d e
    (fun chi rho => if alpha ≤ rho.re then zeroMultiplicity chi rho else 0)
  simp only [paper_induced_mem_iff hN hq hd] at h
  simp only [familyCount, count]
  simp only [Applications.values_eq_complete_filter _ ha, Finset.sum_filter,
    retainedCount, zeroMultiplicity] at h ⊢
  by_cases hdiv : d.modulus ∣ q
  · simp only [hdiv, if_true, true_and, show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from
      paper_source_multiplicity hN hd hdiv] at h ⊢
    exact h
  · simpa only [hdiv, false_and, if_false, add_zero] using h

theorem paper_source_numeric_from_density {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h14000 : retainedCount q (bulkCap N) (omegaCutoff N q) d e ≤ 14000)
    (h13 : retainedCount q (cap N 0.33) (omegaCutoff N q) d e ≤ 13)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) :
    lowSum N q - (if d.modulus ∣ q then weight N e.re else 0) ≤ 8.2e-10 / sourceL N := by
  rw [paper_source_low_split hN hq hd, add_sub_cancel_right]
  have h := cutMass_le_three_steps (source_endpoint_ge_thousand hN) (omegaCutoff N q)
    (bulkCap N) (cap N 0.33) (cap N 0.3221)
    (cap_positive hN (by norm_num)) (cap_positive hN (by norm_num))
    (fun chi => retainedValues chi (omegaCutoff N q) d e)
    (fun _ => Finset.filter_subset _ _) hregion
  change retainedSum N q (omegaCutoff N q) d e ≤
    bulkSum N q (omegaCutoff N q) (bulkCap N) +
      weight N (cap N 0.33) * retainedCount q (bulkCap N) (omegaCutoff N q) d e +
      weight N (cap N 0.3221) * retainedCount q (cap N 0.33) (omegaCutoff N q) d e at h
  have hp : 0 < sourceL N := by linarith [sourceL_ge_3100 hN]
  have h1 := mul_le_mul (weight_033_payment hN) (Nat.cast_le.mpr h14000 : (_ : ℝ) ≤ 14000)
    (Nat.cast_nonneg _) (by positivity)
  have h2 := mul_le_mul (weight_03221_payment hN) (Nat.cast_le.mpr h13 : (_ : ℝ) ≤ 13)
    (Nat.cast_nonneg _) (by positivity)
  apply h.trans
  calc
    _ ≤ 6e-10 / sourceL N + (9.486e-15 / sourceL N) * 14000 +
        (2.5296e-14 / sourceL N) * 13 :=
      add_le_add (add_le_add (source_bulk_numeric hN hq) h1) h2
    _ ≤ _ := by
      apply (le_div_iff₀ hp).mpr
      field_simp
      norm_num

theorem paper_source_Jrho_split {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e) (eta : ℝ) :
    (∑ chi : Character q, CompleteExpansion.zeroValueSum chi N (omegaCutoff N q) eta) =
      (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
        (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta) +
          if d.modulus ∣ q then Jrho N e eta else 0 := by
  have h := sum_split_retained (q := q) (omegaCutoff N q) d e
    (fun chi rho => (zeroMultiplicity chi rho : ℂ) * Jrho N rho eta)
  simp only [paper_induced_mem_iff hN hq hd] at h
  by_cases hdiv : d.modulus ∣ q
  · simpa only [CompleteExpansion.zeroValueSum, zeroMultiplicity, if_pos hdiv,
      show analyticOrderNatAt (inducedAt d q).LFunction e = 1 from paper_source_multiplicity hN hd hdiv,
      Nat.cast_one, one_mul] using h
  · simpa only [CompleteExpansion.zeroValueSum, zeroMultiplicity, if_neg hdiv] using h

theorem paper_source_Jrho_numeric {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {d : PrimitiveQuadraticDatum} {e : ℂ} (hd : PaperSource N d e)
    (h14000 : retainedCount q (bulkCap N) (omegaCutoff N q) d e ≤ 14000)
    (h13 : retainedCount q (cap N 0.33) (omegaCutoff N q) d e ≤ 13)
    (hregion : ∀ (chi : Character q) (rho : ℂ),
      rho ∈ retainedValues chi (omegaCutoff N q) d e → rho.re ≤ cap N 0.3221) (eta : ℝ) :
    (∑ chi : Character q, ∑ rho ∈ retainedValues chi (omegaCutoff N q) d e,
      (zeroMultiplicity chi rho : ℝ) * ‖Jrho N rho eta‖) ≤
        (N : ℝ) * (8.2e-10 / sourceL N) := by
  have hw := paper_source_numeric_from_density hN hq hd h14000 h13 hregion
  rw [paper_source_low_split hN hq hd, add_sub_cancel_right] at hw
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Character q)))
    (fun chi _ => subset_Jrho_le (nat_pos_of_exp_le hN) chi (omegaCutoff N q) eta
      (retainedValues chi (omegaCutoff N q) d e) (Finset.filter_subset _ _))
  rw [← Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _))

end LiuWang.Proof.WeightedLowZeros.Continuation
