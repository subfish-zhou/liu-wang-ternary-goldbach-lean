import LiuWang.Proof.Campaign20260915.ThirdDomainTail.NonrealFubini
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.SparseBands

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount hiding heightKernel
open LiuWang.Proof.SourceRoute.SecondArc
open LiuWang.Proof.SourceRoute.SecondArc.Continuation
open LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1

namespace LiuWang.Proof.Campaign20260915.ThirdDomainTail

theorem second_count_above_c1_eq_real {q : ℕ} [NeZero q]
    {alpha y : ℝ} (hy : 0 ≤ y) (ha : siegelCutoff q y < alpha)
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    familyCount q alpha y = familyCount q alpha 0 := by
  have he (chi : Character q) : zeroValues chi alpha y = zeroValues chi alpha 0 := by
    ext rho
    simp only [mem_zeroValues]
    constructor
    · rintro ⟨hz, ⟨h0, h1, hh⟩, hα⟩
      have hr := hlocal chi rho hz h0 h1 hh (ha.trans_le hα)
      exact ⟨hz, ⟨h0, h1, by simp [hr]⟩, hα⟩
    · rintro ⟨hz, ⟨h0, h1, hh⟩, hα⟩
      exact ⟨hz, ⟨h0, h1, hh.trans hy⟩, hα⟩
  simp only [familyCount, count, he]

theorem second_c1_tail_eq_real {q : ℕ} [NeZero q] {X y : ℝ}
    (hy : 0 ≤ y) (hlog : 0 < Real.log ((q : ℝ) * y))
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    (∫ alpha in siegelCutoff q y..1,
      alphaKernel X alpha * (familyCount q alpha y : ℝ)) =
      ∫ alpha in siegelCutoff q y..1,
        alphaKernel X alpha * (familyCount q alpha 0 : ℝ) := by
  have hc : siegelCutoff q y ≤ 1 :=
    sub_le_self _ (div_nonneg (by norm_num) (by positivity))
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ (fun alpha halpha => by
    rw [Set.uIoc_of_le hc] at halpha
    rw [second_count_above_c1_eq_real hy halpha.1 hlocal])

theorem second_full_strip_eq_truncated_add_real {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q))
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    (∫ alpha in stripUpper q y..1,
      alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) =
      (∫ alpha in stripUpper q y..siegelCutoff q y,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) +
      ∫ alpha in siegelCutoff q y..1,
        alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha 0 : ℝ) := by
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have ho := sparse_cutoff_order (middle_log_domain hN hq hy).2.1
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable (q := q) hx ho.2.1 y)
    (count_alpha_integrable hx ho.2.2.le y)
  rw [second_c1_tail_eq_real
    ((middle_height_domain hN hq).1.le.trans hy.1)
    (by linarith [(middle_log_domain hN hq hy).2.1]) hlocal] at hs
  exact hs.symm

theorem second_nonreal_full_strip_eq_truncated {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q))
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    (∫ alpha in stripUpper q y..1, alphaKernel (0.001 * (N : ℝ)) alpha *
      ((familyCount q alpha y : ℝ) - (familyCount q alpha 0 : ℝ))) =
      ∫ alpha in stripUpper q y..siegelCutoff q y,
        alphaKernel (0.001 * (N : ℝ)) alpha *
          ((familyCount q alpha y : ℝ) - (familyCount q alpha 0 : ℝ)) := by
  have hn := natCast_pos_of_exp_le hN
  have hx : 0 < 0.001 * (N : ℝ) := by positivity
  have ho := sparse_cutoff_order (middle_log_domain hN hq hy).2.1
  have hs := second_full_strip_eq_truncated_add_real hN hq hy hlocal
  have hr := intervalIntegral.integral_add_adjacent_intervals
    (count_alpha_integrable (q := q) hx ho.2.1 0)
    (count_alpha_integrable hx ho.2.2.le 0)
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub
      (count_alpha_integrable hx (ho.2.1.trans ho.2.2.le) y)
      (count_alpha_integrable hx (ho.2.1.trans ho.2.2.le) 0),
    intervalIntegral.integral_sub
      (count_alpha_integrable hx ho.2.1 y) (count_alpha_integrable hx ho.2.1 0)]
  linarith only [hs, hr]

theorem second_nonreal_countIntegral_le_truncated {q : ℕ} [NeZero q]
    {X a y : ℝ} (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hac : a ≤ siegelCutoff q y)
    (hy : 0 ≤ y) (hlog : 0 < Real.log ((q : ℝ) * y))
    (hlocal : ∀ (chi : Character q) (rho : ℂ),
      chi.LFunction rho = 0 → 0 < rho.re → rho.re < 1 → |rho.im| ≤ y →
      1 - 1 / (9.645908801 * Real.log ((q : ℝ) * y)) < rho.re → rho.im = 0) :
    SourceRoute.ThirdArc.Continuation.countIntegral q X y a 1 -
        SourceRoute.ThirdArc.Continuation.countIntegral q X 0 a 1 ≤
      SourceRoute.ThirdArc.Continuation.countIntegral q X y a (siegelCutoff q y) := by
  have hx : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hc : siegelCutoff q y ≤ 1 :=
    sub_le_self _ (div_nonneg (by norm_num) (by positivity))
  have hs := SourceRoute.ThirdArc.Continuation.countIntegral_split q y hx ha hac hc
  have hr := SourceRoute.ThirdArc.Continuation.countIntegral_split q 0 hx ha hac hc
  have ht :
      SourceRoute.ThirdArc.Continuation.countIntegral q X y (siegelCutoff q y) 1 =
        SourceRoute.ThirdArc.Continuation.countIntegral q X 0 (siegelCutoff q y) 1 :=
    second_c1_tail_eq_real hy hlog hlocal
  have hn := SourceRoute.ThirdArc.Continuation.countIntegral_nonneg q hX (y := 0) hac
  linarith only [hs, hr, ht, hn]

#print axioms second_c1_tail_eq_real
#print axioms second_full_strip_eq_truncated_add_real
#print axioms second_nonreal_full_strip_eq_truncated
#print axioms second_nonreal_countIntegral_le_truncated

end LiuWang.Proof.Campaign20260915.ThirdDomainTail
