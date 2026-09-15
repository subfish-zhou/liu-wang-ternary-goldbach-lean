import LiuWang.Proof.SourceRoute.LowSum.SourceRows

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.LowSum

theorem coefficient_le_of_rational_test {alpha A : ℝ} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : 1 - 0.001 * (1 + 6 * (1 - alpha)) ≤ A * alpha) :
    coefficient alpha ≤ A := by
  have hid : (0.001 : ℝ) ^ alpha =
      0.001 * Real.exp ((alpha - 1) * Real.log (0.001 : ℝ)) := by
    calc
      _ = Real.exp (Real.log (0.001 : ℝ) + (alpha - 1) * Real.log (0.001 : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        congr 1
        ring
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num)]
  have hm := mul_le_mul_of_nonpos_left log_window_bounds.2 (sub_nonpos.mpr ha1)
  have he := Real.add_one_le_exp ((alpha - 1) * Real.log (0.001 : ℝ))
  unfold coefficient
  apply (div_le_iff₀ ha).mpr
  rw [hid]
  nlinarith

theorem cap_le_one {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    cap N a ≤ 1 := by
  have hl : 0 ≤ Real.log (lowScale N) := by
    linarith [show 25.3294 ≤ Real.log (lowScale N) from original_log_scale_lower (sourceL_ge_3100 hN)]
  unfold cap
  linarith [div_nonneg ha hl]

theorem coefficient_cap_032 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    coefficient (cap N 0.32) ≤ 1.0121 := by
  have hl : 25.3294 ≤ Real.log (lowScale N) := original_log_scale_lower (sourceL_ge_3100 hN)
  have hc : 0.987 ≤ cap N 0.32 := by
    have hd : 0.32 / Real.log (lowScale N) ≤ 0.013 :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    dsimp [cap]
    linarith
  have hp : 0 < cap N 0.32 := by linarith
  exact (coefficient_antitone (by norm_num : (0 : ℝ) < 0.987)
    hp hc).trans
      (coefficient_le_of_rational_test (by norm_num : (0 : ℝ) < 0.987) (by norm_num) (by norm_num))

theorem seed_c1 : 3.0878e-6 ≤ seedExp (1 / 9.645908801) ∧
    seedExp (1 / 9.645908801) ≤ 3.088e-6 := by
  apply seed_enclosure (n := 12) (xl := 0.6880) (xu := 0.68801) <;>
    norm_num [seedRatio, Finset.sum_range_succ, Nat.factorial]

theorem original_215 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    6e-13 / sourceL N +
      (∫ alpha in cap N 0.32..cap N (1 / 9.645908801), 2 * kernel N alpha) ≤
        0.01938 / sourceL N := by
  have h := segment_integral_le_of_coefficient hN
    (a := 0.32) (b := 1 / 9.645908801) (D := 2) (A := 1.0121)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (coefficient_cap_032 hN)
  have hdiff : seedExp (1 / 9.645908801) - seedExp 0.32 ≤ 3.088e-6 - 9.801e-18 := by
    linarith [seed_c1.2, seed_032.1]
  have hnum := mul_le_mul_of_nonneg_left hdiff
    (by norm_num : (0 : ℝ) ≤ 2 * 1.0121 * (25.32942 / 25.3294) * 3100)
  have hp : 0 ≤ sourceL N := by linarith [sourceL_ge_3100 hN]
  apply (add_le_add le_rfl (h.trans (div_le_div_of_nonneg_right hnum hp))).trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) hp

theorem countingFunction_zero_above {ι : Type*} [Fintype ι]
    (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) {c alpha : ℝ}
    (hcap : ∀ i, ∀ rho ∈ Z i, rho.re ≤ c) (ha : c < alpha) :
    countingFunction Z m alpha = 0 := by
  unfold countingFunction
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro rho hr
  obtain ⟨hr, hlow⟩ := Finset.mem_filter.mp hr
  exact False.elim (not_lt_of_ge (hlow.trans (hcap i rho hr)) ha)

theorem counting_integral_zero_above_cap {ι : Type*} [Fintype ι]
    (N : ℕ) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ) {a b : ℝ}
    (hab : a ≤ b) (hcap : ∀ i, ∀ rho ∈ Z i, rho.re ≤ a) :
    (∫ alpha in a..b, kernel N alpha * countingFunction Z m alpha) = 0 := by
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro alpha halpha
  rw [Set.uIoc_of_le hab] at halpha
  rw [countingFunction_zero_above Z m hcap halpha.1, mul_zero]

theorem original_two_zero_tail {ι : Type*} [Fintype ι] {N : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (Z : ι → Finset ℂ) (m : ι → ℂ → ℕ)
    (hrows : ∀ i < 9, countingFunction Z m (cap N (breakpoint i)) ≤ rowCount i)
    (htwo : countingFunction Z m (cap N 0.32) ≤ 2)
    (hcap : ∀ i, ∀ rho ∈ Z i, rho.re ≤ cap N (1 / 9.645908801)) :
    (∫ alpha in bulkCap N..1, kernel N alpha * countingFunction Z m alpha) ≤
      0.01938 / sourceL N := by
  have hn := nat_pos_of_exp_le hN
  have hlow : 0 < cap N 0.478 := by linarith [cap_ge_098 hN (by norm_num : (0.478 : ℝ) ≤ 0.478)]
  have hmid : 0 < cap N 0.32 := by linarith [cap_ge_098 hN (by norm_num : (0.32 : ℝ) ≤ 0.478)]
  have hhigh : 0 < cap N (1 / 9.645908801) := by
    linarith [cap_ge_098 hN (by norm_num : (1 / 9.645908801 : ℝ) ≤ 0.478)]
  have hlm : cap N 0.478 ≤ cap N 0.32 := cap_order hN (by norm_num)
  have hmh : cap N 0.32 ≤ cap N (1 / 9.645908801) := cap_order hN (by norm_num)
  have hh1 : cap N (1 / 9.645908801) ≤ 1 := cap_le_one hN (by norm_num)
  have hmi : (∫ alpha in cap N 0.32..cap N (1 / 9.645908801),
      kernel N alpha * countingFunction Z m alpha) ≤
        ∫ alpha in cap N 0.32..cap N (1 / 9.645908801), 2 * kernel N alpha := by
    apply intervalIntegral.integral_mono_on hmh
      (counting_integrand_integrable hn hmid hmh Z m)
      ((kernel_integrable hn hmid hmh).const_mul 2)
    intro alpha halpha
    rw [mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left
      ((countingFunction_antitone Z m halpha.1).trans htwo)
      (kernel_nonneg hn (hmid.trans_le halpha.1))
  change (∫ alpha in cap N 0.478..1, kernel N alpha * countingFunction Z m alpha) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (counting_integrand_integrable hn hlow (hlm.trans hmh) Z m)
    (counting_integrand_integrable hn hhigh hh1 Z m),
    counting_integral_zero_above_cap N Z m hh1 hcap, add_zero,
    ← intervalIntegral.integral_add_adjacent_intervals
      (counting_integrand_integrable hn hlow hlm Z m)
      (counting_integrand_integrable hn hmid hmh Z m)]
  exact (add_le_add (original_first_nine hN Z m hrows) hmi).trans (original_215 hN)

theorem two_zero_original_from_counts {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (hrows : ∀ i < 9, familyCount q (cap N (breakpoint i)) (omegaCutoff N q) ≤ rowCount i)
    (htwo : familyCount q (cap N 0.32) (omegaCutoff N q) ≤ 2)
    (hcap : ∀ (chi : Character q), ∀ rho ∈ CompleteExpansion.zeroValues chi (omegaCutoff N q),
      rho.re ≤ cap N (1 / 9.645908801)) :
    lowSum N q ≤ 0.0194 / sourceL N := by
  let Z := fun chi : Character q => CompleteExpansion.zeroValues chi (omegaCutoff N q)
  have htail := original_two_zero_tail hN Z zeroMultiplicity
    (fun i hi => by
      rw [countingFunction_full _ (by linarith [cap_ge_098 hN (row_parameters hi).2.2])]
      exact_mod_cast hrows i hi)
    (by
      rw [countingFunction_full _ (by linarith [cap_ge_098 hN (by norm_num : (0.32 : ℝ) ≤ 0.478)])]
      exact_mod_cast htwo)
    hcap
  have h := (subset_original_reduction hN hq Z (fun _ _ hr => hr)).trans (add_le_add le_rfl htail)
  apply h.trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith [sourceL_ge_3100 hN])

end LiuWang.Proof.SourceRoute.LowSum
