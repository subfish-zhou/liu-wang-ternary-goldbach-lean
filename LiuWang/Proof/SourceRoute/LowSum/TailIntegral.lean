import LiuWang.Proof.SourceRoute.LowSum.IntegralBounds

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.WeightedLowZeros
open LiuWang.Proof.WeightedLowZeros.Continuation
open LiuWang.Proof.Parameters

namespace LiuWang.Proof.SourceRoute.LowSum

def seedRatio : ℝ := 3100 / 25.32942

theorem original_log_seed_lower : 25.3294 ≤ Real.log (3.36 * (3100 : ℝ) ^ 3) := by
  apply (Real.le_log_iff_exp_le (by norm_num)).mpr
  have hs := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.3294)
    (by norm_num : (0.3294 : ℝ) ≤ 1) (by norm_num : 0 < (8 : ℕ))
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 25
  calc
    Real.exp 25.3294 = Real.exp 1 ^ 25 * Real.exp 0.3294 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ ≤ (2.7182818286 : ℝ) ^ 25 *
      ((∑ i ∈ Finset.range 8, (0.3294 : ℝ) ^ i / i.factorial) +
        0.3294 ^ 8 * (8 + 1) / ((8 : ℕ).factorial * 8)) :=
      mul_le_mul hp hs (Real.exp_pos _).le (by positivity)
    _ ≤ _ := by norm_num [Finset.sum_range_succ, Nat.factorial]

theorem original_log_scale_lower {L : ℝ} (hL : 3100 ≤ L) :
    25.3294 ≤ Real.log (3.36 * L ^ 3) :=
  original_log_seed_lower.trans (Real.log_le_log (by norm_num)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hL 3) (by norm_num)))

theorem exponential_difference_integral (u a b : ℝ) :
    (∫ t in b..a, u * Real.exp (-t * u)) = Real.exp (-b * u) - Real.exp (-a * u) := by
  calc
    _ = -Real.exp (-a * u) - -Real.exp (-b * u) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _
        have h := (((hasDerivAt_id t).neg.mul_const u).exp).neg
        apply h.congr_deriv
        dsimp
        ring
      · have hc : Continuous (fun t : ℝ => u * Real.exp (-t * u)) := by fun_prop
        exact hc.intervalIntegrable _ _
    _ = _ := by ring

theorem original_difference_decay {L a b : ℝ} (hL : 3100 ≤ L)
    (hb : 0.1 ≤ b) (hba : b ≤ a) (ha : a ≤ 0.478) :
    Real.exp (-b * L / Real.log (3.36 * L ^ 3)) -
        Real.exp (-a * L / Real.log (3.36 * L ^ 3)) ≤
      (25.32942 / 25.3294) * (3100 / L) ^ 4 *
        (Real.exp (-b * seedRatio) - Real.exp (-a * seedRatio)) := by
  let u := L / Real.log (3.36 * L ^ 3)
  let R := (25.32942 / 25.3294) * (3100 / L) ^ 4
  have hp : 0 < L := by linarith
  have hlo := original_log_scale_lower hL
  have hu0 : 0 ≤ u := div_nonneg hp.le (by linarith)
  have hu : u ≤ L / 25.3294 :=
    div_le_div_of_nonneg_left hp.le (by norm_num) hlo
  have hfactor : (L / 25.3294) * (3100 / L) ^ 5 = R * seedRatio := by
    dsimp [R, seedRatio]
    field_simp
  have hi : (∫ t in b..a, u * Real.exp (-t * u)) ≤
      ∫ t in b..a, R * (seedRatio * Real.exp (-t * seedRatio)) := by
    apply intervalIntegral.integral_mono_on hba
    · have hc : Continuous (fun t : ℝ => u * Real.exp (-t * u)) := by fun_prop
      exact hc.intervalIntegrable _ _
    · have hc : Continuous (fun t : ℝ => R * (seedRatio * Real.exp (-t * seedRatio))) := by
        fun_prop
      exact hc.intervalIntegrable _ _
    · intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hd := decay_with_original_log_seed hL (c := t) (s := t * seedRatio)
        (hb.trans ht.1) (by dsimp [seedRatio]; positivity)
        (by dsimp [seedRatio]; linarith [ht.2])
        (by dsimp [seedRatio]; nlinarith) le_rfl
      have he : -t * L / Real.log (3.36 * L ^ 3) = -t * u := by dsimp [u]; ring
      rw [he] at hd
      have hs : -(t * seedRatio) = -t * seedRatio := by ring
      rw [hs] at hd
      calc
        _ ≤ (L / 25.3294) * (Real.exp (-t * seedRatio) * (3100 / L) ^ 5) :=
          mul_le_mul hu hd (Real.exp_pos _).le (by positivity)
        _ = ((L / 25.3294) * (3100 / L) ^ 5) * Real.exp (-t * seedRatio) := by ring
        _ = _ := by rw [hfactor]; ring
  rw [exponential_difference_integral, intervalIntegral.integral_const_mul,
    exponential_difference_integral] at hi
  have hea : -a * L / Real.log (3.36 * L ^ 3) = -a * u := by dsimp [u]; ring
  have heb : -b * L / Real.log (3.36 * L ^ 3) = -b * u := by dsimp [u]; ring
  rw [hea, heb]
  exact hi

theorem cap_order {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a b : ℝ} (hba : b ≤ a) : cap N a ≤ cap N b := by
  have hl : 0 < Real.log (lowScale N) := by
    have := original_log_scale_lower (sourceL_ge_3100 hN)
    change 25.3294 ≤ Real.log (lowScale N) at this
    linarith
  unfold cap
  linarith [div_le_div_of_nonneg_right hba hl.le]

theorem cap_ge_098 {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a : ℝ} (ha : a ≤ 0.478) : 0.98 ≤ cap N a := by
  have hl : 25.3294 ≤ Real.log (lowScale N) :=
    original_log_scale_lower (sourceL_ge_3100 hN)
  have hd : a / Real.log (lowScale N) ≤ 0.02 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  unfold cap
  linarith

theorem cap_power_eq {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) (a : ℝ) :
    (N : ℝ) ^ (cap N a - 1) =
      Real.exp (-a * sourceL N / Real.log (3.36 * sourceL N ^ 3)) := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (nat_pos_of_exp_le hN))]
  congr 1
  dsimp [cap, lowScale, sourceP, sourceL]
  ring

theorem segment_integral_le_of_coefficient {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a b D A : ℝ} (hb : 0.1 ≤ b) (hba : b ≤ a) (ha : a ≤ 0.478) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hcoef : coefficient (cap N a) ≤ A) :
    (∫ alpha in cap N a..cap N b, D * kernel N alpha) ≤
      (D * A * (25.32942 / 25.3294) * 3100 *
        (Real.exp (-b * seedRatio) - Real.exp (-a * seedRatio))) / sourceL N := by
  have hn := nat_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have hp : 0 < sourceL N := by linarith
  have hcap : 0 < cap N a := by linarith [cap_ge_098 hN ha]
  have hdiff0 : 0 ≤ (N : ℝ) ^ (cap N b - 1) - (N : ℝ) ^ (cap N a - 1) :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      (by linarith [cap_order hN hba]))
  have hstep : (∫ alpha in cap N a..cap N b, D * kernel N alpha) ≤
      D * A * ((N : ℝ) ^ (cap N b - 1) - (N : ℝ) ^ (cap N a - 1)) := by
    rw [intervalIntegral.integral_const_mul]
    apply (mul_le_mul_of_nonneg_left
      (integral_kernel_le_endpoint_difference hn hcap (cap_order hN hba)) hD).trans
    nlinarith [mul_le_mul_of_nonneg_right hcoef hdiff0]
  rw [cap_power_eq hN, cap_power_eq hN] at hstep
  have hd := original_difference_decay hL hb hba ha
  have hseed : 0 ≤ Real.exp (-b * seedRatio) - Real.exp (-a * seedRatio) := by
    apply sub_nonneg.mpr (Real.exp_le_exp.mpr _)
    dsimp [seedRatio]
    linarith
  have ht0 : 0 ≤ 3100 / sourceL N := by positivity
  have ht1 : 3100 / sourceL N ≤ 1 := (div_le_one hp).mpr hL
  have hpow : (3100 / sourceL N) ^ 4 ≤ 3100 / sourceL N := by
    have h3 : (3100 / sourceL N) ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
    nlinarith [mul_le_mul_of_nonneg_right h3 ht0,
      show (3100 / sourceL N) ^ 4 = (3100 / sourceL N) ^ 3 * (3100 / sourceL N) by ring]
  calc
    _ ≤ D * A * ((25.32942 / 25.3294) * (3100 / sourceL N) ^ 4 *
        (Real.exp (-b * seedRatio) - Real.exp (-a * seedRatio))) :=
      hstep.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    _ ≤ D * A * ((25.32942 / 25.3294) * (3100 / sourceL N) *
        (Real.exp (-b * seedRatio) - Real.exp (-a * seedRatio))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) hseed) (by positivity)
    _ = _ := by ring

theorem original_segment_integral_le {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ))
    {a b D : ℝ} (hb : 0.1 ≤ b) (hba : b ≤ a) (ha : a ≤ 0.478) (hD : 0 ≤ D) :
    (∫ alpha in cap N a..cap N b, D * kernel N alpha) ≤
      (D * 1.0193 * (25.32942 / 25.3294) * 3100 *
        (Real.exp (-b * seedRatio) - Real.exp (-a * seedRatio))) / sourceL N := by
  apply segment_integral_le_of_coefficient hN hb hba ha hD (by norm_num)
  have hp : 0 < cap N a := by linarith [cap_ge_098 hN ha]
  exact (coefficient_antitone (by norm_num : (0 : ℝ) < 0.98) hp
    (cap_ge_098 hN ha)).trans coefficient_098_bounds.2

end LiuWang.Proof.SourceRoute.LowSum
