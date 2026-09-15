import LiuWang.Proof.Campaign20260915.ZetaValidation.ZetaMellinTail
import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelSourceTail
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

set_option autoImplicit false
noncomputable section
open Complex Set Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

-- This branch has argument in (-pi/2, 3*pi/2), cut along the negative imaginary ray.
def rsHankelLog (z : ℂ) : ℂ := log (-I * z) + Real.pi / 2 * I

def rsHankelNumerator (s : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  exp ((s - 1) * rsHankelLog z - 2 * Real.pi * I * m * z)

def rsHankelDenominator (z : ℂ) : ℂ := exp (2 * Real.pi * I * z) - 1

def rsHankelKernel (s : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  rsHankelNumerator s m z / rsHankelDenominator z

theorem rsHankelLog_analytic {z : ℂ} (hz : z.re ≠ 0) : AnalyticAt ℂ rsHankelLog z := by
  have hi : AnalyticAt ℂ (fun w : ℂ => -I * w) z := by fun_prop
  have hs : -I * z ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simpa using hz
  exact hi.clog hs |>.add analyticAt_const

theorem rsHankelLog_pos {x : ℝ} (hx : 0 < x) :
    rsHankelLog x = Real.log x := by
  unfold rsHankelLog
  rw [log_mul_ofReal x hx (-I) (neg_ne_zero.mpr I_ne_zero), log_neg_I]
  ring

theorem rsHankelLog_neg {x : ℝ} (hx : 0 < x) :
    rsHankelLog (-x) = Real.log x + Real.pi * I := by
  unfold rsHankelLog
  rw [neg_mul_neg, log_mul_ofReal x hx I I_ne_zero, log_I]
  ring

theorem rsHankelNumerator_analytic (s : ℂ) (m : ℕ) {z : ℂ} (hz : z.re ≠ 0) :
    AnalyticAt ℂ (rsHankelNumerator s m) z := by
  exact ((analyticAt_const.mul (rsHankelLog_analytic hz)).sub (by fun_prop)).cexp

theorem rsHankelDenominator_analytic (z : ℂ) : AnalyticAt ℂ rsHankelDenominator z := by
  unfold rsHankelDenominator
  fun_prop

theorem rsHankelDenominator_zero_iff (z : ℂ) :
    rsHankelDenominator z = 0 ↔ ∃ n : ℤ, z = n := by
  rw [rsHankelDenominator, sub_eq_zero, exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hp : (2 * Real.pi * I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    apply (mul_left_cancel₀ hp)
    simpa [mul_comm] using hn
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem rsHankelDenominator_deriv_int (n : ℤ) :
    HasDerivAt rsHankelDenominator (2 * Real.pi * I) n := by
  have h := (((hasDerivAt_id (n : ℂ)).const_mul (2 * Real.pi * I)).cexp).sub_const 1
  change HasDerivAt rsHankelDenominator
    (exp (2 * Real.pi * I * n) * (2 * Real.pi * I * 1)) n at h
  have he : exp (2 * Real.pi * I * n) * (2 * Real.pi * I * 1) = 2 * Real.pi * I := by
    rw [mul_comm (2 * Real.pi * I) (n : ℂ), exp_int_mul_two_pi_mul_I, one_mul, mul_one]
  rwa [he] at h

theorem rsHankelKernel_meromorphic (s : ℂ) (m : ℕ) {z : ℂ} (hz : z.re ≠ 0) :
    MeromorphicAt (rsHankelKernel s m) z :=
  (rsHankelNumerator_analytic s m hz).meromorphicAt.div (rsHankelDenominator_analytic z).meromorphicAt

theorem rsHankelKernel_analytic (s : ℂ) (m : ℕ) {z : ℂ}
    (hz : z.re ≠ 0) (hn : ¬∃ n : ℤ, z = n) :
    AnalyticAt ℂ (rsHankelKernel s m) z :=
  (rsHankelNumerator_analytic s m hz).div (rsHankelDenominator_analytic z)
    (mt (rsHankelDenominator_zero_iff z).mp hn)

theorem rsHankelKernel_pole_limit (s : ℂ) (m : ℕ) {n : ℤ} (hn : n ≠ 0) :
    Tendsto (fun z : ℂ => (z - n) * rsHankelKernel s m z) (𝓝[≠] (n : ℂ))
      (𝓝 (rsHankelNumerator s m n / (2 * Real.pi * I))) := by
  have hz : (n : ℂ).re ≠ 0 := by exact_mod_cast hn
  have hp : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hd := (rsHankelDenominator_deriv_int n).tendsto_slope
  have hd0 : rsHankelDenominator n = 0 := (rsHankelDenominator_zero_iff _).mpr ⟨n, rfl⟩
  have ht := ((rsHankelNumerator_analytic s m hz).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).div hd hp
  have he : (fun z : ℂ => rsHankelNumerator s m z / slope rsHankelDenominator (n : ℂ) z) =
      fun z => (z - n) * rsHankelKernel s m z := by
    funext z
    rw [slope_def_field, hd0, sub_zero, div_div_eq_mul_div, rsHankelKernel]
    ring
  change Tendsto (fun z : ℂ => rsHankelNumerator s m z / slope rsHankelDenominator (n : ℂ) z)
    _ _ at ht
  rwa [he] at ht

theorem rsHankelKernel_residue (s : ℂ) (m : ℕ) {n : ℤ} (hn : n ≠ 0) :
    residue (rsHankelKernel s m) n = rsHankelNumerator s m n / (2 * Real.pi * I) :=
  residue_eq_of_tendsto (rsHankelKernel_pole_limit s m hn)

theorem rsHankelNumerator_pos (s : ℂ) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    rsHankelNumerator s m n = (n : ℂ) ^ (s - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rsHankelNumerator, show rsHankelLog (n : ℂ) = Real.log (n : ℝ) by
    exact rsHankelLog_pos hnR, exp_sub, cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  have he : exp (2 * Real.pi * I * (m : ℂ) * n) = 1 := by
    convert exp_nat_mul_two_pi_mul_I (m * n) using 1
    push_cast
    congr 1
    ring
  rw [he, div_one, show log (n : ℂ) = (Real.log (n : ℝ) : ℂ) by
    exact (ofReal_log hnR.le).symm]
  congr 1
  ring

theorem rsHankelNumerator_neg (s : ℂ) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    rsHankelNumerator s m (-(n : ℂ)) =
      (n : ℂ) ^ (s - 1) * exp (Real.pi * I * (s - 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : exp (2 * Real.pi * I * (m : ℂ) * -(n : ℂ)) = 1 := by
    convert exp_int_mul_two_pi_mul_I (-((m * n : ℕ) : ℤ)) using 1
    push_cast
    congr 1
    ring
  rw [rsHankelNumerator, show rsHankelLog (-(n : ℂ)) =
    Real.log (n : ℝ) + Real.pi * I by exact rsHankelLog_neg hnR, exp_sub, he, div_one,
    mul_add, exp_add, cpow_def_of_ne_zero (by exact_mod_cast hn.ne'),
    show log (n : ℂ) = (Real.log (n : ℝ) : ℂ) by exact (ofReal_log hnR.le).symm]
  congr 1 <;> congr 1 <;> ring

end LiuWang.Proof.Campaign20260915.ZetaValidation
