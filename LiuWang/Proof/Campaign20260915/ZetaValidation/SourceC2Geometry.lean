import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelAnnulusContinuation
import LiuWang.Proof.Campaign20260915.ZetaValidation.SaddleLocalIntegral

set_option autoImplicit false
noncomputable section
open Complex Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

-- The source PDF p. 280 has epsilon/2, not 2*epsilon.
def rsC2Corner (eta : ℝ) : ℂ := rsDescentPoint eta (-eta / 2)

def rsC2LeftDirection (eta : ℝ) (m : ℕ) : ℂ :=
  -((m : ℂ) + 1 / 2) - rsC2Corner eta

def rsC2LeftPoint (eta : ℝ) (m : ℕ) (r : ℝ) : ℂ :=
  rsC2Corner eta + r * rsC2LeftDirection eta m

theorem rsC2Corner_coordinates (eta : ℝ) :
    (rsC2Corner eta).re = eta - eta / (2 * Real.sqrt 2) ∧
      (rsC2Corner eta).im = eta / (2 * Real.sqrt 2) := by
  simp [rsC2Corner, rsDescentPoint, rsDescentDirection]
  constructor <;> ring

theorem rsC2Corner_upper {eta : ℝ} (he : 0 < eta) :
    0 < (rsC2Corner eta).re ∧ 0 < (rsC2Corner eta).im := by
  rw [(rsC2Corner_coordinates eta).1, (rsC2Corner_coordinates eta).2]
  have hs : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hh : eta / (2 * Real.sqrt 2) < eta := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  exact ⟨by linarith, by positivity⟩

theorem rsC2LeftPoint_coordinates (eta r : ℝ) (m : ℕ) :
    (rsC2LeftPoint eta m r).re =
      (1 - r) * (rsC2Corner eta).re - r * (m + 1 / 2) ∧
    (rsC2LeftPoint eta m r).im = (1 - r) * (rsC2Corner eta).im := by
  simp [rsC2LeftPoint, rsC2LeftDirection]
  constructor <;> ring

theorem rsC2LeftPoint_endpoints (eta : ℝ) (m : ℕ) :
    rsC2LeftPoint eta m 0 = rsC2Corner eta ∧
      rsC2LeftPoint eta m 1 = -((m : ℂ) + 1 / 2) := by
  simp [rsC2LeftPoint, rsC2LeftDirection]

theorem rsC2Left_no_integer {eta : ℝ} (he : 0 < eta) (m : ℕ) (r : ℝ) :
    ¬∃ n : ℤ, rsC2LeftPoint eta m r = n := by
  rintro ⟨n, hn⟩
  have hi := congrArg Complex.im hn
  rw [(rsC2LeftPoint_coordinates eta r m).2] at hi
  simp only [intCast_im] at hi
  have hr : r = 1 := by
    have hh := (mul_eq_zero.mp hi).resolve_right (rsC2Corner_upper he).2.ne'
    linarith
  rw [hr, (rsC2LeftPoint_endpoints eta m).2] at hn
  have h := congrArg Complex.re hn
  have h' : -((m : ℝ) + 1 / 2) = n := by simpa using h
  have hz : 2 * (n : ℤ) + 2 * (m : ℤ) = -1 := by
    have hh : 2 * (n : ℝ) + 2 * (m : ℝ) = -1 := by linarith
    exact_mod_cast hh
  omega

theorem rsC2Left_avoids_cut {eta : ℝ} (he : 0 < eta) (m : ℕ) (r : ℝ) :
    0 < (rsC2LeftPoint eta m r).im ∨ (rsC2LeftPoint eta m r).re ≠ 0 := by
  obtain ⟨hcR, hcI⟩ := rsC2Corner_upper he
  by_cases hr : r < 1
  · left
    rw [(rsC2LeftPoint_coordinates eta r m).2]
    exact mul_pos (by linarith) hcI
  · right
    rw [(rsC2LeftPoint_coordinates eta r m).1]
    have hfirst : (1 - r) * (rsC2Corner eta).re ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hcR.le
    have hr0 : 0 < r := by linarith
    have hsecond : 0 < r * ((m : ℝ) + 1 / 2) := by positivity
    linarith

theorem rsHankelKernel_analytic_slit (s : ℂ) (m : ℕ) {z : ℂ}
    (hz : 0 < z.im ∨ z.re ≠ 0) (hn : ¬∃ n : ℤ, z = n) :
    AnalyticAt ℂ (rsHankelKernel s m) z := by
  have hs : -I * z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    simpa using hz
  have hl : AnalyticAt ℂ rsHankelLog z :=
    (show AnalyticAt ℂ (fun w : ℂ => -I * w) z by fun_prop).clog hs |>.add analyticAt_const
  exact ((analyticAt_const.mul hl).sub (by fun_prop)).cexp.div
    (rsHankelDenominator_analytic z) (mt (rsHankelDenominator_zero_iff _).mp hn)

theorem rsC2Left_kernel_analytic (s : ℂ) {eta : ℝ} (he : 0 < eta) (m : ℕ) (r : ℝ) :
    AnalyticAt ℂ (rsHankelKernel s m) (rsC2LeftPoint eta m r) :=
  rsHankelKernel_analytic_slit s m (rsC2Left_avoids_cut he m r) (rsC2Left_no_integer he m r)

theorem rsC2Right_kernel_analytic (s : ℂ) {eta y : ℝ} (he : 0 < eta)
    (hint : ∀ n : ℤ, eta ≠ n) (hy : -eta / 2 ≤ y) (m : ℕ) :
    AnalyticAt ℂ (rsHankelKernel s m) (rsDescentPoint eta y) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hre : (rsDescentPoint eta y).re = eta + y / Real.sqrt 2 := by
    simp [rsDescentPoint, rsDescentDirection]
    field_simp
  have hy' : -eta / (2 * Real.sqrt 2) ≤ y / Real.sqrt 2 := by
    simpa only [div_div] using div_le_div_of_nonneg_right hy hs.le
  rw [neg_div] at hy'
  have hcr := (rsC2Corner_upper he).1
  rw [(rsC2Corner_coordinates eta).1] at hcr
  exact rsHankelKernel_analytic s m (by rw [hre]; linarith) (rsDescent_no_integer eta y hint)

end LiuWang.Proof.Campaign20260915.ZetaValidation
