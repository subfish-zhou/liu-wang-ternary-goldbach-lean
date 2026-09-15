import LiuWang.Proof.Campaign20260915.Density.SharpCriticalWindow

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

namespace LiuWang.Proof.Campaign20260915.Density

theorem sharp_critical_polynomial_integrable (a L : ℝ) :
    IntegrableOn (fun u : ℝ => sourceKernel u * sharpCriticalPolynomial a L u) (Ioi 0) := by
  convert! kernel_quadratic_integrable (0.0002 * (2.906 * L - 2.4 * a))
    ((2.906 + 0.0002 * 2.19021) * L - 2.4 * a) (2.19021 * L) using 1
  ext u
  unfold sharpCriticalPolynomial
  ring

theorem sharp_critical_polynomial_kernel {a L : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) :
    (4 + (10 : ℝ) ^ (-7 : ℤ)) * 16.016 * a *
      (∫ u in Ioi (0 : ℝ), sourceKernel u * sharpCriticalPolynomial a L u) ≤ 235 * L ^ 2 := by
  have hL : 0 ≤ L := ha.trans haL
  have he (u : ℝ) : sourceKernel u * sharpCriticalPolynomial a L u =
      sourceKernel u * (0.0002 * (2.906 * L - 2.4 * a) +
        ((2.906 + 0.0002 * 2.19021) * L - 2.4 * a) * u + (2.19021 * L) * u ^ 2) := by
    unfold sharpCriticalPolynomial
    ring
  have hb : 0 ≤ (2.906 + 0.0002 * 2.19021) * L - 2.4 * a := by linarith
  have hk := kernel_quadratic_bound (a := 0.0002 * (2.906 * L - 2.4 * a))
    (b := (2.906 + 0.0002 * 2.19021) * L - 2.4 * a) (c := 2.19021 * L) hb (by positivity)
  have hJ : (∫ u in Ioi (0 : ℝ), sourceKernel u * sharpCriticalPolynomial a L u) ≤
      4.979 * L - 1.32 * a := by
    simp_rw [he]
    apply hk.trans
    norm_num
    linarith
  have hp : a * (4.979 * L - 1.32 * a) ≤ 3.659 * L ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr haL)
      (show 0 ≤ 3.659 * L - 1.32 * a by linarith)
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_left hJ
    (show 0 ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) * 16.016 * a by positivity)
  have h' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (4 + (10 : ℝ) ^ (-7 : ℤ)) * 16.016 by positivity)
  norm_num at h h' ⊢
  nlinarith only [h, h', sq_nonneg L]

theorem sharp_critical_kernel_integrable (q : ℕ) (y : ℝ) :
    IntegrableOn (fun u => sourceKernel u * sharpCriticalWindowBudget q y u) (Ioi 0) := by
  unfold IntegrableOn
  have h1 := (sharp_critical_polynomial_integrable (Real.log q) (Real.log ((q : ℝ) * y))).const_mul
    (16.016 * q * Real.sqrt q * y ^ 2 * Real.log q)
  have h2 := (kernel_moment_integrable 1).const_mul (2002 * q * y)
  convert! h1.fun_add h2 using 1
  ext u
  simp only [pow_one]
  unfold sharpCriticalWindowBudget
  ring

theorem source_sharp_critical_kernel (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      (∫ u in Ioi (0 : ℝ), sourceKernel u * sharpCriticalWindowBudget q y u) ≤
      235.69 * (q : ℝ) * Real.sqrt q * y ^ 2 * Real.log ((q : ℝ) * y) ^ 2 := by
  let C : ℝ := 4 + (10 : ℝ) ^ (-7 : ℤ)
  let D : ℝ := (q : ℝ) * Real.sqrt q * y ^ 2
  let L : ℝ := Real.log ((q : ℝ) * y)
  let J : ℝ := ∫ u in Ioi (0 : ℝ),
    sourceKernel u * sharpCriticalPolynomial (Real.log q) L u
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 < y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hLq := Real.log_nonneg hq
  have hLy := Real.log_nonneg (show 1 ≤ y by linarith)
  have hL := source_product_log_ge_eleven q hy
  have haL : Real.log q ≤ L := by dsimp [L]; rw [Real.log_mul hq0.ne' hy0.ne']; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he (u : ℝ) : sourceKernel u * sharpCriticalWindowBudget q y u =
      (16.016 * D * Real.log q) * (sourceKernel u * sharpCriticalPolynomial (Real.log q) L u) +
      (2002 * q * y) * (sourceKernel u * u) := by
    dsimp [D, L]
    unfold sharpCriticalWindowBudget
    ring
  have h2 : IntegrableOn (fun u : ℝ => (2002 * q * y) * (sourceKernel u * u)) (Ioi 0) := by
    simpa only [IntegrableOn, pow_one] using (kernel_moment_integrable 1).const_mul (2002 * q * y)
  have hi : (∫ u in Ioi (0 : ℝ), sourceKernel u * sharpCriticalWindowBudget q y u) =
      (16.016 * D * Real.log q) * J + (2002 * q * y) * (Real.log 3 / 2) := by
    simp_rw [he]
    rw [integral_add ((sharp_critical_polynomial_integrable (Real.log q) L).const_mul _) h2,
      integral_const_mul, integral_const_mul, kernel_moment_one]
  have hmain := mul_le_mul_of_nonneg_left (sharp_critical_polynomial_kernel hLq haL) hD
  have hsmall : C * ((2002 * q * y) * (Real.log 3 / 2)) ≤ 4405 * q * y := by
    have h := mul_le_mul_of_nonneg_left
      (show Real.log 3 / 2 ≤ 0.55 by linarith [Real.log_three_lt_d9])
      (show 0 ≤ C * (2002 * q * y) by dsimp [C]; positivity)
    dsimp [C] at h ⊢
    norm_num at h ⊢
    nlinarith [show 0 ≤ (q : ℝ) * y by positivity]
  have hs : (1 : ℝ) ≤ Real.sqrt q :=
    (Real.le_sqrt (by norm_num) hq0.le).mpr (by simpa using hq)
  have hbase : 10000 * q * y ≤ D := by
    have h := mul_nonneg (show 0 ≤ (q : ℝ) * y by positivity)
      (show 0 ≤ Real.sqrt q * y - 10000 by nlinarith)
    dsimp [D]
    nlinarith only [h]
  have hpay : 4405 * q * y ≤ 0.5 * D := by
    nlinarith [show 0 ≤ (q : ℝ) * y by positivity]
  have hL2 : 1 ≤ L ^ 2 := by dsimp [L]; nlinarith only [hL]
  have hrest := mul_le_mul_of_nonneg_left hL2 hD
  rw [hi]
  change D * (C * 16.016 * Real.log q * J) ≤ D * (235 * L ^ 2) at hmain
  have hfinal : C * ((16.016 * D * Real.log q) * J + (2002 * q * y) * (Real.log 3 / 2)) ≤
      235.69 * D * L ^ 2 := by
    nlinarith only [hmain, hsmall, hpay, hrest, hD]
  dsimp only [C, D, L] at hfinal
  nlinarith only [hfinal]

#print axioms source_sharp_critical_kernel

end LiuWang.Proof.Campaign20260915.Density
