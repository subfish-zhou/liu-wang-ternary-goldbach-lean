import LiuWang.Proof.NearOneDensity.Mass
import LiuWang.Proof.NearOneDensity.TableCertificates
import LiuWang.Proof.ZeroRegionFamily.Sharp.Principal

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open LiuWang.Proof.ZeroRegionFamily
open LiuWang.Proof.ZeroRegionFamily.Sharp

namespace LiuWang.Proof.NearOneDensity

theorem logKernel_eq_dampedLogDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ τ c t : ℝ) :
    logKernel σ τ c χ t = dampedLogDeriv χ σ τ c t := by
  simp only [logKernel, dampedLogDeriv, logDeriv, Pi.div_apply, neg_div, Complex.neg_re,
    mul_comm (t : ℂ) Complex.I]
  ring

theorem damped_mass_eq_zetaDamped {σ : ℝ} (hσ : 1 < σ) :
    (∑' n, dampedWeight σ (stechkinSigma σ) stechkinK n) = zetaDamped σ 0 := by
  rw [damped_mass_eq_zeta hσ (hσ.trans_le (stechkinSigma_ge hσ))]
  simp only [zetaDamped, Complex.ofReal_zero, mul_zero, add_zero, logDeriv,
    Pi.div_apply, neg_div, Complex.neg_re]
  ring

theorem stechkinK_ge_447 : (447 / 1000 : ℝ) ≤ stechkinK := by
  have h := kappa_le_rational
  dsimp [stechkinK]
  linarith

theorem sharp_small_sigma_mass {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) :
    zetaDamped σ 0 ≤ 1 / (σ - 1) - 719 / 800 := by
  have hτ : stechkinSigma σ ≤ 1633 / 1000 := by
    have he := stechkinSigma_equation σ
    have hg := stechkinSigma_ge hσ
    have hsquare : σ ^ 2 ≤ (203 / 200 : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hden : 0 < stechkinSigma σ - 1 := by linarith [stechkinSigma_ge hσ]
  have hquot : (7 / 10 : ℝ) ≤ stechkinK / (stechkinSigma σ - 1) :=
    (le_div_iff₀ hden).mpr (by linarith [stechkinK_ge_447])
  linarith [zeta_real_function hσ (by linarith : σ ≤ 23 / 20)]

theorem row_sigma_bounds (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    1 < 1 + rowA r / Real.log z ∧ 1 + rowA r / Real.log z ≤ 203 / 200 := by
  have hL := source_log_lower hz
  have ha := (row_basic_certificate r).1
  have hmax : rowA r ≤ 0.365 := by cases r <;> norm_num [rowA]
  have hp : 0 < rowA r / Real.log z := div_pos ha (by linarith)
  have hu : rowA r / Real.log z ≤ 3 / 200 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  constructor <;> linarith

theorem row_actual_mass_bound (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    let σ := 1 + rowA r / Real.log z
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re -
        stechkinK * (-deriv riemannZeta (stechkinSigma σ : ℂ) /
          riemannZeta (stechkinSigma σ : ℂ)).re ≤
      Real.log z * massBudget (rowA r) (1 / Real.log z) := by
  dsimp only
  have hσ := row_sigma_bounds r hz
  have h := sharp_small_sigma_mass hσ.1 hσ.2
  have hL : Real.log z ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (source_log_lower hz))
  have ha := (row_basic_certificate r).1.ne'
  have he : 1 / (1 + rowA r / Real.log z - 1) -
      (0.8973 : ℝ) = Real.log z * massBudget (rowA r) (1 / Real.log z) := by
    unfold massBudget
    field_simp [ha, hL]
    ring
  rw [← he]
  simp only [zetaDamped, Complex.ofReal_zero, mul_zero, add_zero, logDeriv, Pi.div_apply,
    neg_div, Complex.neg_re] at h ⊢
  linarith

theorem row_weight_mass_bound (r : DensityRow) {z : ℝ} (hz : 100000000000 ≤ z) :
    let σ := 1 + rowA r / Real.log z
    (∑' n, dampedWeight σ (stechkinSigma σ) stechkinK n) ≤
      Real.log z * massBudget (rowA r) (1 / Real.log z) := by
  dsimp only
  rw [damped_mass_eq_zeta (row_sigma_bounds r hz).1
    ((row_sigma_bounds r hz).1.trans_le (stechkinSigma_ge (row_sigma_bounds r hz).1))]
  exact row_actual_mass_bound r hz

end LiuWang.Proof.NearOneDensity
