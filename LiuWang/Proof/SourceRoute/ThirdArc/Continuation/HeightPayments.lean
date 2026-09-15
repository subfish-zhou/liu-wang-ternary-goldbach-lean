import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.TablePayments
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.LogSubstitution

/-! Integrating the admitted near-one payment through the original height windows. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation

theorem countIntegral_nonneg (q : ℕ) [NeZero q] {X y a b : ℝ}
    (hX : 1 ≤ X) (hab : a ≤ b) : 0 ≤ countIntegral q X y a b := by
  apply intervalIntegral.integral_nonneg hab
  intro alpha _
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hX))
    (Nat.cast_nonneg _)

theorem countIntegral_mono_upper (q : ℕ) [NeZero q] {X y a b c : ℝ}
    (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    countIntegral q X y a b ≤ countIntegral q X y a c := by
  rw [countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX) ha hab hbc]
  exact le_add_of_nonneg_right (countIntegral_nonneg q hX hbc)

theorem countIntegral_mono_height (q : ℕ) [NeZero q] {X a b : ℝ}
    (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    Monotone (fun y => countIntegral q X y a b) := by
  intro y z hyz
  have hx : 0 < X := lt_of_lt_of_le zero_lt_one hX
  apply intervalIntegral.integral_mono_on hab (family_beta_integrable q y hx ha hab)
    (family_beta_integrable q z hx ha hab)
  intro alpha _
  have hcount : familyCount q alpha y ≤ familyCount q alpha z :=
    Finset.sum_le_sum (fun chi _ => count_mono_height chi alpha hyz)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
    (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg hX))

theorem M3_moving_remainder_monotone {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) {X u v : ℝ}
    (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v) :
    MonotoneOn (fun y => countIntegral q X y (59 / 60)
      (rowCutoff .r0478 ((q : ℝ) * y))) (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  intro y hy z _hz hyz
  have hlowy := hu.trans hy.1
  have hlogy : 0 < Real.log ((q : ℝ) * y) := by
    linarith [M3_log_product_ge_thirty hN hq hlowy]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  have hlog := Real.log_le_log (mul_pos hqpos (lowHeight_pos.trans_le hlowy))
    (mul_le_mul_of_nonneg_left hyz hqpos.le)
  have hcut : rowCutoff .r0478 ((q : ℝ) * y) ≤ rowCutoff .r0478 ((q : ℝ) * z) :=
    sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num [rowLambda]) hlogy hlog) 1
  exact (countIntegral_mono_height q hX (by norm_num)
    (M3_rowCutoff_ge_source_split .r0478 hN hq hlowy) hyz).trans
      (countIntegral_mono_upper q hX (by norm_num)
        (M3_rowCutoff_ge_source_split .r0478 hN hq hlowy) hcut)

theorem heightKernel_mul_integrable {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (p : ℝ)
    {F : ℝ → ℝ} (hF : IntervalIntegrable F volume u v) :
    IntervalIntegrable (fun y => heightKernel p y * F y) volume u v := by
  have hk : ContinuousOn (heightKernel p) (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    intro y hy
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const y (-p - 1)
        (Or.inl (hu.trans_le hy.1).ne'))).continuousWithinAt
  simpa only [mul_comm] using hF.mul_continuousOn hk

theorem M3_threeRowPrice_continuousOn {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (X d : ℝ) {u v : ℝ} (hu : lowHeight ≤ u) (huv : u ≤ v) :
    ContinuousOn (fun y => threeRowPrice X ((q : ℝ) * y) d) (Set.uIcc u v) := by
  rw [Set.uIcc_of_le huv]
  intro y hy
  have hlow := hu.trans hy.1
  have hz : 0 < (q : ℝ) * y := by linarith [(M3_table_domain hN hq hlow).1]
  have hl : Real.log ((q : ℝ) * y) ≠ 0 := by
    linarith [M3_log_product_ge_thirty hN hq hlow]
  have hc (c : ℝ) : ContinuousAt
      (fun y => Real.exp (-c * Real.log X / Real.log ((q : ℝ) * y))) y := by
    have hd : ContinuousAt (fun y => -c * Real.log X / Real.log ((q : ℝ) * y)) y :=
      continuousAt_const.div ((continuousAt_const.mul continuousAt_id).log hz.ne') hl
    exact Real.continuous_exp.continuousAt.comp hd
  exact ((((hc 0.36).sub (hc 0.478)).const_mul 14000).add
    (((hc 0.33).sub (hc 0.36)).const_mul 20) |>.add
    (((hc d).sub (hc 0.33)).const_mul 13)).continuousWithinAt

theorem M3_height_integral_split_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) {X u v p : ℝ}
    (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∫ y in u..v, heightKernel p y * countIntegral q X y (59 / 60) 1) ≤
      (∫ y in u..v, heightKernel p y * countIntegral q X y (59 / 60)
        (rowCutoff .r0478 ((q : ℝ) * y))) +
      ∫ y in u..v, heightKernel p y * threeRowPrice X ((q : ℝ) * y) 0 := by
  have hpos := lowHeight_pos.trans_le hu
  have hfull := heightKernel_mul_integrable hpos huv p
    (countIntegral_mono_height q hX (by norm_num : (1 : ℝ) / 2 ≤ 59 / 60)
      (by norm_num : (59 : ℝ) / 60 ≤ 1)).intervalIntegrable
  have hrem := heightKernel_mul_integrable hpos huv p
    (M3_moving_remainder_monotone hN hq hX hu huv).intervalIntegrable
  have hprice := heightKernel_mul_integrable hpos huv p
    (M3_threeRowPrice_continuousOn hN hq X 0 hu huv).intervalIntegrable
  rw [← intervalIntegral.integral_add hrem hprice]
  apply intervalIntegral.integral_mono_on huv hfull (hrem.add hprice)
  intro y hy
  have h := mul_le_mul_of_nonneg_left (M3_countIntegral_split_paid hN hq hX (hu.trans hy.1))
    (mul_nonneg hp (Real.rpow_nonneg (hpos.trans_le hy.1).le (-p - 1)))
  simpa only [heightKernel, mul_add, rowCutoff, rowLambda] using h

theorem M3_height_near_integral_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) {X u v p : ℝ}
    (hX : 1 ≤ X) (hu : lowHeight ≤ u) (huv : u ≤ v) (hp : 0 ≤ p) :
    (∫ y in u..v, heightKernel p y * countIntegral q X y
        (rowCutoff .r0478 ((q : ℝ) * y)) 1) ≤
      ∫ y in u..v, heightKernel p y * threeRowPrice X ((q : ℝ) * y) 0 := by
  have hpos := lowHeight_pos.trans_le hu
  have hfull := heightKernel_mul_integrable hpos huv p
    (countIntegral_mono_height q hX (by norm_num : (1 : ℝ) / 2 ≤ 59 / 60)
      (by norm_num : (59 : ℝ) / 60 ≤ 1)).intervalIntegrable
  have hrem := heightKernel_mul_integrable hpos huv p
    (M3_moving_remainder_monotone hN hq hX hu huv).intervalIntegrable
  have heq : (∫ y in u..v, heightKernel p y * countIntegral q X y
      (rowCutoff .r0478 ((q : ℝ) * y)) 1) =
      (∫ y in u..v, heightKernel p y * countIntegral q X y (59 / 60) 1) -
      ∫ y in u..v, heightKernel p y * countIntegral q X y (59 / 60)
        (rowCutoff .r0478 ((q : ℝ) * y)) := by
    rw [← intervalIntegral.integral_sub hfull hrem]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le huv] at hy
    dsimp only
    rw [countIntegral_split q y (lt_of_lt_of_le zero_lt_one hX) (by norm_num)
      (M3_rowCutoff_ge_source_split .r0478 hN hq (hu.trans hy.1))
      (rowCutoff_le_one .r0478 (M3_table_domain hN hq (hu.trans hy.1)).1)]
    ring
  rw [heq]
  linarith [M3_height_integral_split_paid hN hq hX hu huv hp]

theorem threeRowPrice_log_substitution (q : ℕ) [NeZero q] {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (X p : ℝ) :
    (∫ y in u..v, heightKernel p y * threeRowPrice X ((q : ℝ) * y) 0) =
      p * (q : ℝ) ^ p * ∫ t in Real.log ((q : ℝ) * u)..Real.log ((q : ℝ) * v),
        Real.exp (-p * t) *
          (14000 * (Real.exp (-0.36 * Real.log X / t) - Real.exp (-0.478 * Real.log X / t)) +
          20 * (Real.exp (-0.33 * Real.log X / t) - Real.exp (-0.36 * Real.log X / t)) +
          13 * (1 - Real.exp (-0.33 * Real.log X / t))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
  rw [height_log_substitution hq hu hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have he : (q : ℝ) * (Real.exp t / q) = Real.exp t := by field_simp
  simp only [threeRowPrice, he, Real.log_exp, neg_zero, zero_mul, zero_div, Real.exp_zero]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation
