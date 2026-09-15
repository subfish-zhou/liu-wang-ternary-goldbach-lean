import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5ActualCount
import LiuWang.Proof.Campaign20260915.ThirdBudgets.EndpointDensityScalar

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.SourceRoute.ThirdArc
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart
open LiuWang.Proof.SourceRoute.ThirdArc.Continuation.ScalarPayment.Restart.OriginalV1
open LiuWang.Proof.WeightedLowZeros.Continuation

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

theorem endpoint_density_count_bound {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (sourceCutoff q 0.478 (legalHeight q (middleHeight N q))),
      (familyCount q alpha (legalHeight q (middleHeight N q)) : ℝ) ≤
        sourceDensity q (legalHeight q (middleHeight N q)) alpha) :
    countIntegral q (0.001 * N) (middleHeight N q) (59 / 60)
        (sourceCutoff q 0.478 (middleHeight N q)) ≤
      500000 * Real.log (10 * Real.pi * sourceL N ^ 7) ^ 6 *
        Real.exp (-0.478 * (sourceL N - 7) / Real.log (10 * Real.pi * sourceL N ^ 7)) := by
  let U := middleHeight N q
  let g := legalHeight q U
  let s := Real.log ((q : ℝ) * U)
  let z := Real.log ((q : ℝ) * g)
  have hh := original_height_order (exp_2000_le_of_exp_3100_le hN) hq1
  have hy : U ∈ Set.Icc (middleHeight N q) (sourceT N) := ⟨le_rfl, hh.2⟩
  have hd := m5_legal_height_domain hN hq hq1 hy
  have hs0 : 0 < s := (middle_endpoint_log_ratio hN).1
  have hz : 36 ≤ z := hd.2.2.2.2.1
  have hzs : z ≤ (11 / 10) * s := hd.2.2.2.2.2.1
  have hX : (1 : ℝ) < 0.001 * N := by linarith [Real.add_one_le_exp (3100 : ℝ)]
  have hlogX := LiuWang.Proof.SourceRoute.SecondArc.log_window_lower hN
  have hL := sourceL_ge_3100 hN
  have hL0 : 0 < sourceL N := by linarith
  have he : (q : ℝ) * U = 10 * Real.pi * sourceL N ^ 7 := by
    dsimp only [U, middleHeight]
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  have hs : s = Real.log (10 * Real.pi) + 7 * Real.log (sourceL N) := by
    dsimp only [s]
    rw [he, Real.log_mul (by positivity : (10 * Real.pi : ℝ) ≠ 0)
      (pow_pos hL0 7).ne', Real.log_pow]
    norm_num
  have hgap : 4 * z ≤ Real.log (0.001 * (N : ℝ)) / 10 := by
    have hl := (div_le_iff₀ hL0).mp (log_over_self_bound hL)
    linarith [M6Certificate.log_ten_pi_bounds.2]
  have hcut := (sourceCutoff_order hN hq hh.1 (d := 0.478) (e := 0.478)
    (by norm_num) le_rfl le_rfl).1
  have hc :
      countIntegral q (0.001 * N) g (59 / 60) (sourceCutoff q 0.478 U) ≤
        (10 / 9) * (16541 + 9 * 24200) * z ^ 6 *
          Real.exp (-0.478 * Real.log (0.001 * N) / s) := by
    calc
      _ ≤ ∫ alpha in (59 / 60 : ℝ)..(sourceCutoff q 0.478 U),
          betaKernel (0.001 * N) alpha * sourceDensity q g alpha := by
        apply intervalIntegral.integral_mono_on hcut
          (family_beta_integrable q g (by linarith) (by norm_num) hcut)
          (((betaKernel_continuous (by linarith : (0 : ℝ) < 0.001 * N)).mul
            (sourceDensity_continuous (NeZero.pos q) (by linarith [hd.2.2.2.1])
              (by linarith : 0 < z))).intervalIntegrable _ _)
        intro alpha halpha
        exact mul_le_mul_of_nonneg_left
          (hdensity alpha ⟨halpha.1, halpha.2.trans (m5_cutoff_le_legal hN hq1 hy)⟩)
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg hX.le))
      _ ≤ _ := source_density_integral_bound (NeZero.pos q) hX hd.2.2.2.1
        hs0 hz hzs hgap hcut
  have hcount := (ThirdDomainTail.countIntegral_le_legal_height q hX.le
    (by norm_num) hcut).trans hc
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ z) hzs 6
  rw [mul_pow] at hpow
  have hcoeff : (10 / 9 : ℝ) * (16541 + 9 * 24200) * z ^ 6 ≤ 500000 * s ^ 6 := by
    nlinarith only [hpow, pow_nonneg hs0.le 6]
  have hexp : Real.exp (-0.478 * Real.log (0.001 * N) / s) ≤
      Real.exp (-0.478 * (sourceL N - 7) / s) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) hs0.le
  have hp := mul_le_mul hcoeff hexp (Real.exp_pos _).le (by positivity)
  have h := hcount.trans hp
  dsimp only [s] at h
  rwa [he] at h

theorem endpoint_density_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (sourceCutoff q 0.478 (legalHeight q (middleHeight N q))),
      (familyCount q alpha (legalHeight q (middleHeight N q)) : ℝ) ≤
        sourceDensity q (legalHeight q (middleHeight N q)) alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60)
          (sourceCutoff q 0.478 (middleHeight N q)) ≤
      0.022449 * (N : ℝ) / sourceL N := by
  let L := sourceL N
  let D := 500000 * Real.log (10 * Real.pi * L ^ 7) ^ 6 *
    Real.exp (-0.478 * (L - 7) / Real.log (10 * Real.pi * L ^ 7))
  have hL : 3100 ≤ L := sourceL_ge_3100 hN
  have hL0 : 0 < L := by linarith
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcount := endpoint_density_count_bound hN hq hq1 hdensity
  have hn := htotient.trans (hnu.trans (m5_nu_scaling hL))
  have hroot : 0 < Real.sqrt (10 * Real.pi * L ^ 7) := by positivity
  have hden : 0 < 250 * L ^ 3 := by positivity
  have hcoef :
      16 * N * ((q : ℝ) / q.totient) / Real.sqrt (10 * Real.pi * L ^ 7) ≤
        (N : ℝ) / L * ((16 * 7.56 / (250 * 3100) : ℝ) / L) := by
    calc
      _ ≤ 16 * N * (7.56 * (L / 3100)) / Real.sqrt (10 * Real.pi * L ^ 7) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) hroot.le
      _ ≤ 16 * N * (7.56 * (L / 3100)) / (250 * L ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) hden (middle_endpoint_sqrt_lower hL)
      _ = _ := by field_simp
  calc
    _ ≤ (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) * D :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (16 * N * ((q : ℝ) / q.totient) / Real.sqrt (10 * Real.pi * L ^ 7)) * D := by
      rw [middle_endpoint_coefficient hN]
    _ ≤ ((N : ℝ) / L * ((16 * 7.56 / (250 * 3100) : ℝ) / L)) * D :=
      mul_le_mul_of_nonneg_right hcoef hD
    _ = (N : ℝ) / L * (((16 * 7.56 / (250 * 3100) : ℝ) / L) * D) := by ring
    _ ≤ (N : ℝ) / L * 0.022449 :=
      mul_le_mul_of_nonneg_left (endpoint_density_scalar_paid hL) (by positivity)
    _ = _ := by dsimp only [L]; ring

theorem middle_endpoint_original_paid {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : sourceP N ≤ (q : ℝ))
    (hq1 : (q : ℝ) ≤ sourceP1 N)
    (hdensity : ∀ alpha ∈ Set.Icc (59 / 60 : ℝ)
      (sourceCutoff q 0.478 (legalHeight q (middleHeight N q))),
      (familyCount q alpha (legalHeight q (middleHeight N q)) : ℝ) ≤
        sourceDensity q (legalHeight q (middleHeight N q)) alpha)
    (htotient : (q : ℝ) / q.totient ≤ sourceNu q)
    (hnu : sourceNu q ≤ sourceNu (sourceL N ^ 6)) :
    (16 * N * Real.sqrt q / q.totient / Real.sqrt (middleHeight N q)) *
        countIntegral q (0.001 * N) (middleHeight N q) (59 / 60) 1 ≤
      0.02245 * (N : ℝ) / sourceL N := by
  have h := middle_endpoint_density_remainder hN hq hq1 htotient hnu
  have hp := endpoint_density_original_paid hN hq hq1 hdensity htotient hnu
  unfold sourceCutoff at hp
  ring_nf at h hp ⊢
  linarith only [h, hp]

#print middle_endpoint_original_paid
#print axioms endpoint_density_original_paid
#print axioms middle_endpoint_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
