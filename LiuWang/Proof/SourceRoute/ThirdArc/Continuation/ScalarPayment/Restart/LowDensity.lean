import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityIntegral
import LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.DensityScalar
import LiuWang.Proof.DirichletZeroCount.Transport

/-! The original (5.24) interval is paid; the actual Theorem 7 count input remains explicit. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount

namespace LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart

def lowDensityBill (N q : ℕ) : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) * lowCoefficient (59 / 60) *
    ∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      betaKernel N alpha * sourceDensity q (10000 * Real.log q) alpha

theorem density_scalar_paid {L z : ℝ} (hL : 3100 ≤ L) {q : ℕ} (hq : 0 < q)
    (hs : 0 < Real.log ((q : ℝ) * lowHeight)) (hz : 0 ≤ z)
    (hzs : z ≤ (11 / 10) * Real.log ((q : ℝ) * lowHeight)) :
    (Real.sqrt q / q.totient) * (60 / 59) * (10 / 9) * (16541 + 9 * 24200) *
        z ^ 6 * Real.exp (-0.478 * L / Real.log ((q : ℝ) * lowHeight)) ≤
      0.24981 / L := by
  have hLp : 0 < L := by linarith
  have hp := pow_le_pow_left₀ hz hzs 6
  rw [mul_pow] at hp
  have hc := density_coupled_decay hL hq hs
  have he := (mul_le_mul_of_nonneg_left hc
    (by norm_num : (0 : ℝ) ≤ (60 / 59) * (10 / 9) * (16541 + 9 * 24200) * (11 / 10) ^ 6)).trans
    (by simpa only [mul_assoc] using density_endpoint_certificate)
  apply (le_div_iff₀ hLp).mpr
  have hp := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ L * (Real.sqrt q / q.totient) * (60 / 59) * (10 / 9) *
      (16541 + 9 * 24200) * Real.exp (-0.478 * L / Real.log ((q : ℝ) * lowHeight)) by positivity)
  nlinarith only [hp, he]

theorem equation_5_24_explicit {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    lowDensityBill N q ≤ 0.24981 * (N : ℝ) / sourceL N := by
  have hx := natCast_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have hqR : (0 : ℝ) < q := lt_of_lt_of_le (pow_pos (by linarith : 0 < sourceL N) 3) hq
  have hqn : 0 < q := Nat.cast_pos.mp hqR
  let : NeZero q := ⟨by omega⟩
  have hh := M3_density_logs hN hq hq1
  have hs : 0 < Real.log ((q : ℝ) * lowHeight) := by
    linarith [M3_log_product_ge_thirty hN hq le_rfl]
  have ha : (59 / 60 : ℝ) ≤ 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) :=
    M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  have hX : (1 : ℝ) < N := by
    have h := Real.add_one_le_exp (3100 : ℝ)
    linarith
  have hi := source_density_integral_bound hqn hX
    (show 1 ≤ 10000 * Real.log q by linarith [hh.1]) hs hh.2.1 hh.2.2.1 hh.2.2.2 ha
  have hc : lowCoefficient (59 / 60) ≤ 60 / 59 := by
    simpa using lowCoefficient_le_inverse (by norm_num : (0 : ℝ) < 59 / 60)
  have hcn : 0 ≤ lowCoefficient (59 / 60) := lowCoefficient_nonneg (by norm_num)
  have hu : 0 ≤ (10 / 9) * (16541 + 9 * 24200) *
      Real.log ((q : ℝ) * (10000 * Real.log q)) ^ 6 *
        Real.exp (-0.478 * Real.log (N : ℝ) / Real.log ((q : ℝ) * lowHeight)) := by positivity
  have hpaid := density_scalar_paid hL hqn hs (by linarith [hh.2.1]) hh.2.2.1
  unfold lowDensityBill
  calc
    _ ≤ ((N : ℝ) * Real.sqrt q / q.totient) * lowCoefficient (59 / 60) *
        ((10 / 9) * (16541 + 9 * 24200) *
          Real.log ((q : ℝ) * (10000 * Real.log q)) ^ 6 *
            Real.exp (-0.478 * Real.log (N : ℝ) / Real.log ((q : ℝ) * lowHeight))) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ ((N : ℝ) * Real.sqrt q / q.totient) * (60 / 59) *
        ((10 / 9) * (16541 + 9 * 24200) *
          Real.log ((q : ℝ) * (10000 * Real.log q)) ^ 6 *
            Real.exp (-0.478 * Real.log (N : ℝ) / Real.log ((q : ℝ) * lowHeight))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hu
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hpaid hx.le
      dsimp only [sourceL] at h ⊢
      ring_nf at h ⊢
      exact h

theorem enlarged_height_source_domain {N q : ℕ}
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N) :
    lowHeight ≤ 10000 * Real.log q ∧
      max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ 10000 * Real.log q := by
  have ht := (M3_density_logs hN hq hq1).1
  have hL := sourceL_ge_3100 hN
  have hqR : (0 : ℝ) < q := lt_of_lt_of_le (pow_pos (by linarith : 0 < sourceL N) 3) hq
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast Nat.cast_pos.mp hqR
  constructor
  · unfold lowHeight
    nlinarith [Real.pi_lt_four]
  · rw [max_le_iff]
    refine ⟨?_, le_rfl⟩
    have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 100000)
      (by norm_num : (0 : ℝ) < 1) hq1R
    norm_num at hd
    linarith

theorem low_count_integral_le_densityBill {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha) :
    ((N : ℝ) * Real.sqrt q / q.totient) *
      (∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
        betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      lowDensityBill N q := by
  have hx := natCast_pos_of_exp_le hN
  have hL := sourceL_ge_3100 hN
  have hh := M3_density_logs hN hq hq1
  have hqR : (0 : ℝ) < q := lt_of_lt_of_le (pow_pos (by linarith : 0 < sourceL N) 3) hq
  have ha : (59 / 60 : ℝ) ≤ 1 - 0.478 / Real.log ((q : ℝ) * lowHeight) :=
    M3_rowCutoff_ge_source_split .r0478 hN hq le_rfl
  have hy := (enlarged_height_source_domain hN hq hq1).1
  have hcont := (betaKernel_continuous hx).mul
    (sourceDensity_continuous (Nat.cast_pos.mp hqR)
      (by linarith [hh.1] : 0 < 10000 * Real.log q) (by linarith [hh.2.1]))
  have hi : (∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight) ≤
      lowCoefficient (59 / 60) *
        (∫ alpha in (59 / 60 : ℝ)..(1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
          betaKernel N alpha * sourceDensity q (10000 * Real.log q) alpha) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ha
      (family_low_integrable q lowHeight hx (by norm_num : (1 : ℝ) / 2 ≤ 59 / 60) ha)
      (hcont.const_mul _ |>.intervalIntegrable _ _)
    intro alpha halpha
    have hm : familyCount q alpha lowHeight ≤ familyCount q alpha (10000 * Real.log q) :=
      Finset.sum_le_sum fun chi _ => count_mono_height chi alpha hy
    have hmR : (familyCount q alpha lowHeight : ℝ) ≤ sourceDensity q (10000 * Real.log q) alpha :=
      (by exact_mod_cast hm : (familyCount q alpha lowHeight : ℝ) ≤
        familyCount q alpha (10000 * Real.log q)).trans (hdensity alpha halpha)
    have hc := lowCoefficient_antitone (by norm_num : (0 : ℝ) < 59 / 60) halpha.1
    have hk : 0 ≤ betaKernel N alpha := by
      unfold betaKernel
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (by change 0 ≤ sourceL N; linarith)
    have hp := mul_le_mul hc hmR (Nat.cast_nonneg _) (lowCoefficient_nonneg (by norm_num))
    have hp := mul_le_mul_of_nonneg_left hp hk
    dsimp only [Pi.mul_apply]
    nlinarith only [hp]
  have h := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (N : ℝ) * Real.sqrt q / q.totient by positivity)
  unfold lowDensityBill
  simpa only [mul_assoc] using h

def exceptionalTailBill (N q : ℕ) [NeZero q] : ℝ :=
  ((N : ℝ) * Real.sqrt q / q.totient) *
    ∫ alpha in (1 - 0.2067 / Real.log ((q : ℝ) * lowHeight))..1,
      betaKernel N alpha * lowCoefficient alpha * familyCount q alpha lowHeight

theorem sigma4_three_source_pieces_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (1 - 0.478 / Real.log ((q : ℝ) * lowHeight)),
      (familyCount q alpha (10000 * Real.log q) : ℝ) ≤
        sourceDensity q (10000 * Real.log q) alpha) :
    sigma4 N q ≤ 0.25349 * (N : ℝ) / sourceL N + exceptionalTailBill N q := by
  have h := sigma4_two_source_pieces_paid hN hq hq1
  have hi := (low_count_integral_le_densityBill hN hq hq1 hdensity).trans
    (equation_5_24_explicit hN hq hq1)
  unfold remainingLowBill at h
  unfold exceptionalTailBill
  ring_nf at h hi ⊢
  linarith only [h, hi]

end LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
