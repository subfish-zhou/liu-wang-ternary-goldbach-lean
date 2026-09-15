import LiuWang.Proof.Campaign20260915.ZetaValidation.RiemannSiegelSaddle
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
noncomputable section
open Complex Metric
open scoped NNReal ENNReal

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsSaddleCoefficient (sigma lambda : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n (rsSaddleWeight sigma lambda) 0 / n.factorial

def rsSaddleMajorant (sigma lambda R : ℝ) : ℝ :=
  Real.exp (3 / 2 * |sigma - 1| * (R / lambda) +
    2 / 3 * lambda ^ 2 * (R / lambda) ^ 3)

theorem rsSaddle_differentiable_closedBall (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR : R < lambda) :
    DifferentiableOn ℂ (rsSaddleWeight sigma lambda) (closedBall 0 R) := by
  intro z hz
  exact (rsSaddle_analytic sigma hl ((by simpa using hz : ‖z‖ ≤ R).trans_lt hR)).differentiableAt.differentiableWithinAt

theorem rsSaddle_sphere_bound (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR : R ≤ lambda / 2) {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖rsSaddleWeight sigma lambda z‖ ≤ rsSaddleMajorant sigma lambda R := by
  have he : ‖z‖ = R := by simpa using hz
  have h := rsSaddle_weight_bound sigma hl (he.le.trans hR)
  simpa only [rsSaddleMajorant, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hl, he] using h

theorem rsSaddle_coefficient_bound (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ lambda / 2) (n : ℕ) :
    ‖rsSaddleCoefficient sigma lambda n‖ ≤ rsSaddleMajorant sigma lambda R / R ^ n := by
  have hd := rsSaddle_differentiable_closedBall sigma hl (by linarith : R < lambda)
  have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
    (fun z hz => rsSaddle_sphere_bound sigma hl hR hz)
  rw [rsSaddleCoefficient, norm_div, norm_natCast]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf]
  exact hc.trans_eq (by ring)

theorem rsSaddle_hasSum (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R < lambda)
    {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n => rsSaddleCoefficient sigma lambda n * z ^ n)
      (rsSaddleWeight sigma lambda z) := by
  let radius : ℝ≥0 := ⟨R, hR0.le⟩
  have hd := rsSaddle_differentiable_closedBall sigma hl hR
  have hp := hd.hasFPowerSeriesOnBall (R := radius) (by exact hR0)
  have hz' : z ∈ eball (0 : ℂ) (radius : ℝ≥0∞) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    exact hz
  have h := hp.hasSum_iteratedFDeriv hz'
  simp only [zero_add] at h
  convert! h using 1
  funext n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  unfold rsSaddleCoefficient
  ring

theorem rsSaddle_taylor_remainder (sigma : ℝ) {lambda R : ℝ}
    (hl : 0 < lambda) (hR0 : 0 < R) (hR : R ≤ lambda / 2)
    {z : ℂ} (hz : ‖z‖ < R) (N : ℕ) :
    ‖rsSaddleWeight sigma lambda z -
      ∑ n ∈ Finset.range N, rsSaddleCoefficient sigma lambda n * z ^ n‖ ≤
        rsSaddleMajorant sigma lambda R * (‖z‖ / R) ^ N / (1 - ‖z‖ / R) := by
  have hs := rsSaddle_hasSum sigma hl hR0 (by linarith : R < lambda) hz
  have ht := (hasSum_nat_add_iff' N).mpr hs
  have hr0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR0.le
  have hr1 : ‖z‖ / R < 1 := (div_lt_one hR0).mpr hz
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (rsSaddleMajorant sigma lambda R * (‖z‖ / R) ^ N)
  rw [← div_eq_mul_inv] at hg
  apply ht.norm_le_of_bounded hg
  intro n
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (rsSaddleMajorant sigma lambda R / R ^ (n + N)) * ‖z‖ ^ (n + N) :=
      mul_le_mul_of_nonneg_right (rsSaddle_coefficient_bound sigma hl hR0 hR _) (by positivity)
    _ = _ := by rw [div_pow, pow_add, pow_add]; ring

theorem rsSaddle_coefficient_zero (sigma lambda : ℝ) :
    rsSaddleCoefficient sigma lambda 0 = 1 := by
  simp [rsSaddleCoefficient, rsSaddle_zero]

theorem rsSaddle_coefficient_one (sigma : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    rsSaddleCoefficient sigma lambda 1 = ((sigma - 1 : ℝ) : ℂ) / lambda := by
  simpa [rsSaddleCoefficient] using rsSaddle_first_deriv sigma hl

end LiuWang.Proof.Campaign20260915.ZetaValidation
