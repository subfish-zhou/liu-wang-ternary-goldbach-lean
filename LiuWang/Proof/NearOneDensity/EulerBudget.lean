import LiuWang.Proof.NearOneDensity.SelectedCosts

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity

theorem primeCost_le_rational_power {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    primeCost p σ ≤ Real.log p * (1 / ((p : ℝ) - 1) - stechkinK / ((p : ℝ) ^ 2 - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hge : (p : ℝ) ≤ (p : ℝ) ^ σ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1.le hσ.le
  have hτ := stechkinSigma_bounds hσ (by linarith : σ ≤ 23 / 20)
  have hτ0 : 1 < (p : ℝ) ^ stechkinSigma σ :=
    Real.one_lt_rpow hp1 (by linarith [hτ.1])
  have hτ2 : (p : ℝ) ^ stechkinSigma σ ≤ (p : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hp1.le
      (show stechkinSigma σ ≤ 2 by linarith [hτ.2])
  have ha := one_div_le_one_div_of_le (show 0 < (p : ℝ) - 1 by linarith)
    (show (p : ℝ) - 1 ≤ (p : ℝ) ^ σ - 1 by linarith)
  have hb := one_div_le_one_div_of_le (show 0 < (p : ℝ) ^ stechkinSigma σ - 1 by linarith)
    (show (p : ℝ) ^ stechkinSigma σ - 1 ≤ (p : ℝ) ^ 2 - 1 by linarith)
  have hh := mul_le_mul_of_nonneg_left hb stechkinK_mem.1
  rw [primeCost_eq_positive_power hp]
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg p)
  simpa only [mul_one_div] using sub_le_sub ha hh

theorem primeCost_log_budget {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    primeCost p σ ≤ stechkinConductorCoeff * Real.log p +
      (if p = 2 then 161 / 400 else 0) + (if p = 3 then 297 / 1600 else 0) := by
  have hb := primeCost_le_rational_power hp hσ hσ₁
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  by_cases h2 : p = 2
  · subst p
    norm_num at hb ⊢
    have hlog : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have hprod := mul_le_mul_of_nonneg_right stechkinK_le (Real.log_natCast_nonneg 2)
    have hprod' := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 23 / 40)
    unfold stechkinConductorCoeff
    nlinarith
  by_cases h3 : p = 3
  · subst p
    norm_num at hb ⊢
    have hlog : Real.log 3 ≤ 11 / 10 := by linarith [Real.log_three_lt_d9]
    have hprod := mul_le_mul_of_nonneg_right stechkinK_le (Real.log_natCast_nonneg 3)
    have hprod' := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 27 / 160)
    unfold stechkinConductorCoeff
    nlinarith
  · simp only [if_neg h2, if_neg h3, add_zero]
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp.five_le_of_ne_two_of_ne_three h2 h3
    have hden : 0 < (p : ℝ) - 1 := by linarith
    have hrec : 1 / ((p : ℝ) - 1) ≤ stechkinConductorCoeff := by
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
        (show 4 ≤ (p : ℝ) - 1 by linarith)
      linarith
    have hpos : 0 ≤ stechkinK / ((p : ℝ) ^ 2 - 1) :=
      div_nonneg stechkinK_mem.1 (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left (show
      1 / ((p : ℝ) - 1) - stechkinK / ((p : ℝ) ^ 2 - 1) ≤ stechkinConductorCoeff by linarith)
      (Real.log_natCast_nonneg p)
    nlinarith

theorem finite_primeCost_budget (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    (∑ p ∈ s, primeCost p σ) ≤
      stechkinConductorCoeff * (∑ p ∈ s, Real.log p) + 941 / 1600 := by
  have hh := Finset.sum_le_sum (fun p hp => primeCost_log_budget (hs p hp) hσ hσ₁)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have h2 : (∑ p ∈ s, if p = 2 then (161 / 400 : ℝ) else 0) ≤ 161 / 400 := by
    simp only [Finset.sum_ite_eq']
    split <;> norm_num
  have h3 : (∑ p ∈ s, if p = 3 then (297 / 1600 : ℝ) else 0) ≤ 297 / 1600 := by
    simp only [Finset.sum_ite_eq']
    split <;> norm_num
  linarith

theorem disjoint_prime_support_log {q d : ℕ} (hq : 0 < q) (hd : 0 < d) (hdq : d ∣ q)
    (s : Finset ℕ) (hs : s ⊆ q.primeFactors) (hcop : ∀ p ∈ s, p.Coprime d) :
    Real.log d + (∑ p ∈ s, Real.log p) ≤ Real.log q := by
  have hp (p) (hps : p ∈ s) : p.Prime := Nat.prime_of_mem_primeFactors (hs hps)
  have hprod : (∏ p ∈ s, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset s q.primeFactors id hs).trans (Nat.prod_primeFactors_dvd q)
  have hc : (∏ p ∈ s, p).Coprime d := Nat.coprime_prod_left_iff.mpr hcop
  have hdiv := hc.symm.mul_dvd_of_dvd_of_dvd hdq hprod
  have hbound : (d : ℝ) * (∏ p ∈ s, (p : ℝ)) ≤ q := by
    have hh : ((d * ∏ p ∈ s, p : ℕ) : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq hdiv
    simpa only [Nat.cast_mul, Nat.cast_prod] using hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpR : 0 < ∏ p ∈ s, (p : ℝ) :=
    Finset.prod_pos (fun p hps => by exact_mod_cast (hp p hps).pos)
  have hh := Real.log_le_log (mul_pos hdR hpR) hbound
  rwa [Real.log_mul hdR.ne' hpR.ne',
    Real.log_prod (fun p hps => by exact_mod_cast (hp p hps).ne_zero)] at hh

theorem badPrimeCost_paid {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    badPrimeCost χ σ ≤
      stechkinConductorCoeff * (Real.log q - Real.log χ.conductor) + 941 / 1600 := by
  let s := q.primeFactors.filter (fun p : ℕ => χ.primitiveCharacter p ≠ 0)
  have hs : s ⊆ q.primeFactors := Finset.filter_subset _ _
  have hc (p) (hp : p ∈ s) : p.Coprime χ.conductor := by
    have hh := (Finset.mem_filter.mp hp).2
    exact (ZMod.isUnit_iff_coprime p χ.conductor).mp (MulChar.apply_ne_zero_iff.mp hh)
  have hlog := disjoint_prime_support_log (NeZero.pos q)
    (Nat.pos_of_ne_zero χ.conductor_ne_zero) χ.conductor_dvd_level s hs hc
  have hk : 0 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_mem.2]
  have hmul := mul_le_mul_of_nonneg_left hlog hk
  have hcost := finite_primeCost_budget s
    (fun p hp => Nat.prime_of_mem_primeFactors (hs hp)) hσ hσ₁
  have he : badPrimeCost χ σ = ∑ p ∈ s, primeCost p σ := by
    simp only [badPrimeCost, s, Finset.sum_filter, ne_eq, ite_not]
  rw [he]
  nlinarith

theorem nonprincipal_row_cross_cost (r : DensityRow) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z t : ℝ}
    (hz : 100000000000 ≤ z)
    (hheight : Real.log q + Real.log (max 1 |t|) ≤ Real.log z + Real.log 2) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK χ t ≤
      Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z) := by
  dsimp only
  rw [logKernel_eq_dampedLogDeriv]
  have hσ := row_sigma_bounds r hz
  have hb := imprimitive_damped_bound χ hχ hσ.1 (by linarith) t
  have hc := badPrimeCost_paid χ hσ.1 hσ.2
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hk' : stechkinConductorCoeff ≤ 277 / 1000 := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_ge_447]
  have hh := mul_le_mul_of_nonneg_left hheight (by linarith : 0 ≤ stechkinConductorCoeff)
  have hpi := mul_le_mul hk log_pi_ge_eleven_tenths (by norm_num)
    (by linarith : 0 ≤ stechkinConductorCoeff)
  have htwo := mul_le_mul hk' (show Real.log 2 ≤ 7 / 10 by linarith [Real.log_two_lt_d9])
    (Real.log_natCast_nonneg 2) (by norm_num : (0 : ℝ) ≤ 277 / 1000)
  have hL : Real.log z ≠ 0 := ne_of_gt (by linarith [source_log_lower hz] : 0 < Real.log z)
  have he : Real.log z * crossBudget stechkinConductorCoeff (1 / Real.log z) =
      stechkinConductorCoeff * Real.log z + 0.7647 := by
    unfold crossBudget
    field_simp
  rw [he]
  nlinarith

end LiuWang.Proof.NearOneDensity
