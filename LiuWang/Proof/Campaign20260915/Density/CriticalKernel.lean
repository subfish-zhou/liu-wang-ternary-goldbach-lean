import LiuWang.Proof.Campaign20260915.Density.FamilyCriticalWindow

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanTransfer
open LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.MeanBudgets

namespace LiuWang.Proof.Campaign20260915.Density

theorem critical_quadratic_integrable (b : ℝ) :
    IntegrableOn (fun u : ℝ =>
      sourceKernel u * (512 * (u + 0.0001) * (2 * u + 4.1 * (1.01 + b)))) (Ioi 0) := by
  convert! kernel_quadratic_integrable (512 * 0.0001 * 4.1 * (1.01 + b))
    (512 * (0.0002 + 4.1 * (1.01 + b))) 1024 using 1
  ext u
  ring

theorem critical_quadratic_kernel {b : ℝ} (hb : 0 ≤ b) :
    (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      (∫ u in Ioi (0 : ℝ),
        sourceKernel u * (512 * (u + 0.0001) * (2 * u + 4.1 * (1.01 + b)))) ≤
      4700 * (b + 2.5) := by
  have he (u : ℝ) :
      sourceKernel u * (512 * (u + 0.0001) * (2 * u + 4.1 * (1.01 + b))) =
        sourceKernel u * (512 * 0.0001 * 4.1 * (1.01 + b) +
          (512 * (0.0002 + 4.1 * (1.01 + b))) * u + 1024 * u ^ 2) := by ring
  simp_rw [he]
  have h := mul_le_mul_of_nonneg_left
    (kernel_quadratic_bound (a := 512 * 0.0001 * 4.1 * (1.01 + b))
      (b := 512 * (0.0002 + 4.1 * (1.01 + b))) (c := 1024)
      (by positivity) (by norm_num))
    (show 0 ≤ 4 + (10 : ℝ) ^ (-7 : ℤ) by positivity)
  apply h.trans
  norm_num
  linarith

theorem critical_log_polynomial {a b : ℝ} (hL : 11 ≤ a + b) :
    4800 * (1 + a) * (1.01 + (a + b)) * (b + 2.5) ≤ 235 * (a + b) ^ 4 := by
  have hprod : (1 + a) * (b + 2.5) ≤ ((a + b) + 3.5) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((1 + a) - (b + 2.5))]
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 4800 * (1.01 + (a + b)) by linarith)
  let x : ℝ := (a + b) - 11
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hp : 0 ≤ 235 * (x + 11) ^ 4 - 1200 * (x + 14.5) ^ 2 * (x + 12.01) := by
    ring_nf
    positivity
  dsimp [x] at hp
  nlinarith only [hm, hp]

theorem critical_kernel_integrable (q : ℕ) (y : ℝ) :
    IntegrableOn (fun u => sourceKernel u * criticalWindowBudget q y u) (Ioi 0) := by
  unfold IntegrableOn
  have h1 := (critical_quadratic_integrable (Real.log y)).const_mul
    ((q : ℝ) * Real.sqrt q * y ^ 2 * (1 + Real.log q) * (1.01 + Real.log ((q : ℝ) * y)))
  have h2 := (kernel_moment_integrable 1).const_mul (4 * q * y)
  convert! h1.fun_add h2 using 1
  ext u
  simp only [pow_one]
  unfold criticalWindowBudget
  ring

theorem source_critical_kernel_bound (q : ℕ) [NeZero q] {y : ℝ}
    (hy : max (100000 / (q : ℝ)) (10000 * Real.log q) ≤ y) :
    (4 + (10 : ℝ) ^ (-7 : ℤ)) *
      (∫ u in Ioi (0 : ℝ), sourceKernel u * criticalWindowBudget q y u) ≤
      235.69 * (q : ℝ) * Real.sqrt q * y ^ 2 * Real.log ((q : ℝ) * y) ^ 4 := by
  let C : ℝ := 4 + (10 : ℝ) ^ (-7 : ℤ)
  let D : ℝ := (q : ℝ) * Real.sqrt q * y ^ 2 *
    (1 + Real.log q) * (1.01 + Real.log ((q : ℝ) * y))
  let J : ℝ := ∫ u in Ioi (0 : ℝ),
    sourceKernel u * (512 * (u + 0.0001) * (2 * u + 4.1 * (1.01 + Real.log y)))
  have hy' : 10000 ≤ y := by
    linarith [(source_height_log_bounds (source_height_ge_log_six hy)).1]
  have hy0 : 0 < y := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := by positivity
  have hLq := Real.log_nonneg hq
  have hLy := Real.log_nonneg (show 1 ≤ y by linarith)
  have hlog : Real.log ((q : ℝ) * y) = Real.log q + Real.log y :=
    Real.log_mul hq0.ne' hy0.ne'
  have hLX : 0 ≤ Real.log ((q : ℝ) * y) := by rw [hlog]; positivity
  have hlarge : 100000 ≤ (q : ℝ) * y := by
    have h := (div_le_iff₀ hq0).mp (max_le_iff.mp hy).1
    nlinarith only [h]
  have hL : 11 ≤ Real.log ((q : ℝ) * y) := by
    have hval : 11 ≤ Real.log 100000 := by
      rw [show (100000 : ℝ) = 10 ^ (5 : ℕ) by norm_num, Real.log_pow,
        show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
    exact hval.trans (Real.log_le_log (by norm_num) hlarge)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have he (u : ℝ) :
      sourceKernel u * criticalWindowBudget q y u =
        D * (sourceKernel u * (512 * (u + 0.0001) *
          (2 * u + 4.1 * (1.01 + Real.log y)))) +
        (4 * q * y) * (sourceKernel u * u) := by
    dsimp [D]
    unfold criticalWindowBudget
    ring
  have h2 : IntegrableOn (fun u : ℝ => (4 * q * y) * (sourceKernel u * u)) (Ioi 0) := by
    simpa only [IntegrableOn, pow_one] using (kernel_moment_integrable 1).const_mul (4 * q * y)
  have hi : (∫ u in Ioi (0 : ℝ), sourceKernel u * criticalWindowBudget q y u) =
      D * J + (4 * q * y) * (Real.log 3 / 2) := by
    simp_rw [he]
    rw [integral_add ((critical_quadratic_integrable (Real.log y)).const_mul D) h2,
      integral_const_mul, integral_const_mul, kernel_moment_one]
  have hmain := mul_le_mul_of_nonneg_left (critical_quadratic_kernel hLy) hD0
  have hsmall : C * ((4 * q * y) * (Real.log 3 / 2)) ≤ 9 * q * y := by
    have h := mul_le_mul_of_nonneg_left
      (show Real.log 3 / 2 ≤ 0.55 by linarith [Real.log_three_lt_d9])
      (show 0 ≤ C * (4 * q * y) by dsimp [C]; positivity)
    dsimp [C] at h ⊢
    norm_num at h ⊢
    nlinarith [show 0 ≤ (q : ℝ) * y by positivity]
  have hs : (1 : ℝ) ≤ Real.sqrt q :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hq)
  have hbase : (q : ℝ) * y ≤ q * Real.sqrt q * y ^ 2 := by
    have hp := mul_nonneg (show 0 ≤ (q : ℝ) * y by positivity)
      (show 0 ≤ Real.sqrt q * y - 1 by nlinarith)
    nlinarith only [hp]
  have hD : (q : ℝ) * y ≤ D := by
    apply hbase.trans
    dsimp [D]
    apply (le_mul_of_one_le_right (by positivity)
      (show 1 ≤ 1 + Real.log q by linarith)).trans
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hrest : 9 * q * y ≤ 100 * D * (Real.log y + 2.5) := by
    nlinarith [mul_nonneg hD0 hLy]
  have hpay : C * (∫ u in Ioi (0 : ℝ), sourceKernel u * criticalWindowBudget q y u) ≤
      4800 * D * (Real.log y + 2.5) := by
    rw [hi]
    change D * (C * J) ≤ D * (4700 * (Real.log y + 2.5)) at hmain
    nlinarith only [hmain, hsmall, hrest]
  have hpoly := critical_log_polynomial (a := Real.log q) (b := Real.log y)
    (by rwa [hlog] at hL)
  rw [← hlog] at hpoly
  have hp := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ (q : ℝ) * Real.sqrt q * y ^ 2 by positivity)
  apply hpay.trans
  dsimp [D]
  have hn : 0 ≤ (q : ℝ) * Real.sqrt q * y ^ 2 * Real.log ((q : ℝ) * y) ^ 4 := by positivity
  nlinarith only [hp, hn]

#print axioms source_critical_kernel_bound

end LiuWang.Proof.Campaign20260915.Density
