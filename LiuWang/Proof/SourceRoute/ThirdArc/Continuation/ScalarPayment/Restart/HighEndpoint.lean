import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.HighEndpointDensity
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.LowDensity
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.SourceWindows

/-! The actual high-height count integral with its original 7e-31 payment. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

theorem countIntegral_le_left_count {q : ℕ} [NeZero q] {X y a b : ℝ}
    (hX : 1 ≤ X) (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    countIntegral q X y a b ≤ familyCount q a y := by
  have hx : 0 < X := by linarith
  calc
    _ ≤ ∫ alpha in a..b, (familyCount q a y : ℝ) * betaKernel X alpha := by
      apply intervalIntegral.integral_mono_on hab
        (family_beta_integrable q y hx ha hab)
        (((betaKernel_continuous hx).const_mul _).intervalIntegrable _ _)
      intro alpha halpha
      have hm : familyCount q alpha y ≤ familyCount q a y :=
        Finset.sum_le_sum fun chi _ => count_antitone_alpha chi y halpha.1
      have hmR : (familyCount q alpha y : ℝ) ≤ familyCount q a y := by exact_mod_cast hm
      have hk : 0 ≤ betaKernel X alpha :=
        mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg hX)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmR hk
    _ = (familyCount q a y : ℝ) * (X ^ (b - 1) - X ^ (a - 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_betaKernel hx]
    _ ≤ _ := by
      have hp : X ^ (b - 1) ≤ (1 : ℝ) := Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
      have h := mul_le_mul_of_nonneg_left
        (show X ^ (b - 1) - X ^ (a - 1) ≤ (1 : ℝ) by linarith [Real.rpow_pos_of_pos hx (a - 1)])
        (Nat.cast_nonneg (α := ℝ) (familyCount q a y))
      simpa only [mul_one] using h

theorem equation_5_41_explicit {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ)) :
    (5 * N * Real.sqrt q / q.totient / sourceT N) *
        highEndpointDensity (sourceL N) ≤
      (7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N := by
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have hf : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hqscale := (div_le_iff₀ hf).mpr (single_zero_totient_scale hN hq)
  have hD : 0 ≤ highEndpointDensity (sourceL N) := by
    unfold highEndpointDensity
    have hl := WeightedLowZeros.Continuation.log_3100_bounds.1.trans
      (Real.log_le_log (by norm_num) hL)
    positivity
  have hp := mul_le_mul_of_nonneg_right hqscale
    (show 0 ≤ 5 * (N : ℝ) * highEndpointDensity (sourceL N) / sourceL N ^ 15 by positivity)
  have hs := mul_le_mul_of_nonneg_left (high_endpoint_scalar_paid hL) (Nat.cast_nonneg (α := ℝ) N)
  apply (le_div_iff₀ hL0).mpr
  dsimp only [sourceT]
  ring_nf at hp hs ⊢
  linarith only [hp, hs]

theorem equation_5_41_actual_count {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60)) :
    (5 * N * Real.sqrt q / q.totient / sourceT N) *
        countIntegral q N (sourceT N) (59 / 60) 1 ≤
      (7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N := by
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast nat_pos_of_exp_le hN
  have hi := countIntegral_le_left_count (q := q) (y := sourceT N) hX
    (by norm_num : (1 : ℝ) / 2 ≤ 59 / 60) (by norm_num : (59 / 60 : ℝ) ≤ 1) le_rfl
  have h := hi.trans (hdensity.trans (high_endpoint_density_envelope hN hq1))
  have hT : 0 ≤ sourceT N := by
    unfold sourceT
    exact pow_nonneg (by linarith [sourceL_ge_3100 hN]) _
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (equation_5_41_explicit hN hq)

theorem high_count_reduction_endpoint_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : (familyCount q (59 / 60) (sourceT N) : ℝ) ≤
      sourceDensity q (sourceT N) (59 / 60)) :
    (5 * N * Real.sqrt q / q.totient) *
      (∫ alpha in (59 / 60 : ℝ)..1, betaKernel N alpha *
        densityBand q alpha (middleHeight N q) (sourceT N) 1) ≤
      (7 / 10 ^ (31 : ℕ)) * (N : ℝ) / sourceL N +
        (5 * N * Real.sqrt q / q.totient) *
          ∫ y in middleHeight N q..sourceT N,
            y ^ (-2 : ℝ) * countIntegral q N y (59 / 60) 1 := by
  have h := mul_le_mul_of_nonneg_left (original_high_count_reduction hN hq1)
    (show 0 ≤ 5 * N * Real.sqrt q / q.totient by positivity)
  have hp := equation_5_41_actual_count hN hq hq1 hdensity
  ring_nf at h hp ⊢
  linarith only [h, hp]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
