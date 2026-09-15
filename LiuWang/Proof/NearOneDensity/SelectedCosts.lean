import LiuWang.Proof.NearOneDensity.WindowGeometry
import LiuWang.Proof.ZeroRegionFamily.RealClosure.Principal

set_option autoImplicit false
noncomputable section

open Complex
open BombieriVinogradov.SiegelWalfisz
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.PrincipalPsi.Quantitative

namespace LiuWang.Proof.NearOneDensity

theorem log_pi_ge_eleven_tenths : (11 / 10 : ℝ) ≤ Real.log Real.pi := by
  have hp := Real.log_le_log (by norm_num : (0 : ℝ) < 31 / 10)
    (show (31 / 10 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d2])
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / (31 / 10))
  rw [Real.log_div (by norm_num) (by norm_num)] at hh
  norm_num at hh
  linarith [Real.log_three_gt_d9]

theorem shiftedGamma_small_sigma {σ : ℝ} (hσ : 1 < σ) (hσ₁ : σ ≤ 203 / 200) (t : ℝ) :
    shiftedGammaDifference σ t ≤ stechkinConductorCoeff * Real.log (max 1 |t|) + 0.0755 := by
  have hge := stechkinSigma_ge hσ
  have hgap := stechkinSigma_sub_le hσ
  have hu := digamma_shift_up_le (a := 1) (b := σ / 2 + 1) le_rfl (by linarith) (t / 2)
  have hl := digamma_shift_down_le (a := σ / 2 + 1) (b := stechkinSigma σ / 2 + 1)
    (by linarith) (by linarith) (t / 2)
  have href := digamma_one_re_le_log_max (t / 2)
  norm_num only [Complex.ofReal_one] at hu
  have hlog : 2 * |t / 2| = |t| := by rw [abs_div]; norm_num; ring
  rw [hlog] at href
  have ha : (Complex.digamma (((σ / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ))).re ≤
      Real.log (max 1 |t|) + 203 / 200 := by linarith
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr stechkinK_mem.2)
  have h2 := mul_le_mul_of_nonneg_left hl stechkinK_mem.1
  have h3 := mul_le_mul_of_nonneg_left hgap stechkinK_mem.1
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hpi := mul_le_mul hk log_pi_ge_eleven_tenths (by norm_num)
    (by linarith : 0 ≤ stechkinConductorCoeff)
  have hcast (u : ℝ) : ((u : ℂ) + I * t) / 2 + 1 =
      (((u / 2 + 1 : ℝ) : ℂ) + I * (t / 2 : ℝ)) := by push_cast; ring
  unfold shiftedGammaDifference
  rw [hcast, hcast]
  dsimp [stechkinConductorCoeff] at *
  nlinarith [stechkinK_ge_447]

theorem source_selected_reciprocal (r : DensityRow) {z lam : ℝ} {ρ : ℂ}
    (hz : 100000000000 ≤ z) (hlam : 0 ≤ lam)
    (hre : 1 - lam / Real.log z ≤ ρ.re) (hright : ρ.re < 1) :
    Real.log z * (1 / (rowA r + lam)) ≤ 1 / (1 + rowA r / Real.log z - ρ.re) := by
  have hL : 0 < Real.log z := by linarith [source_log_lower hz]
  have ha := (row_basic_certificate r).1
  have hu : 0 < 1 + rowA r / Real.log z - ρ.re := by
    linarith [div_pos ha hL]
  have hupper : 1 + rowA r / Real.log z - ρ.re ≤ (rowA r + lam) / Real.log z := by
    rw [add_div]
    linarith
  have hh := one_div_le_one_div_of_le hu hupper
  have he : 1 / ((rowA r + lam) / Real.log z) = Real.log z * (1 / (rowA r + lam)) := by
    field_simp
  rwa [he] at hh

theorem primitive_row_selected_cost (r : DensityRow) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    {z lam : ℝ} {ρ : ℂ} (hz : 100000000000 ≤ z) (hlam : 0 ≤ lam)
    (hlam₁ : lam ≤ rowLambda r) (hzero : χ.LFunction ρ = 0)
    (hre : 1 - lam / Real.log z ≤ ρ.re) (hright : ρ.re < 1)
    (hheight : Real.log q + Real.log (max 1 |ρ.im|) ≤ Real.log z) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK χ ρ.im ≤
      -(Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)) := by
  dsimp only
  rw [logKernel_eq_dampedLogDeriv]
  have hL : 25 ≤ Real.log z := by linarith [source_log_lower hz]
  have hmax := (row_basic_certificate r).2.1
  have hr : 1 / 2 < ρ.re := by
    have hh : lam / Real.log z < 1 / 2 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hσ := row_sigma_bounds r hz
  have hsel := primitive_actual_selected_bound hχ hp hr hzero hσ.1
    (by linarith : 1 + rowA r / Real.log z ≤ 23 / 20)
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hh := mul_le_mul_of_nonneg_left hheight (by linarith : 0 ≤ stechkinConductorCoeff)
  have hpi := mul_le_mul hk log_pi_ge_one (by norm_num) (by linarith : 0 ≤ stechkinConductorCoeff)
  have hrec := source_selected_reciprocal r hz hlam hre hright
  have he : -(Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)) =
      stechkinConductorCoeff * Real.log z + 0.0755 - Real.log z * (1 / (rowA r + lam)) := by
    unfold zeroBudget
    field_simp
    ring
  rw [he]
  nlinarith

theorem nonprincipal_inducing_row_selected_cost (r : DensityRow) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1)
    {z lam : ℝ} {ρ : ℂ} (hz : 100000000000 ≤ z) (hlam : 0 ≤ lam)
    (hlam₁ : lam ≤ rowLambda r) (hzero : χ.LFunction ρ = 0)
    (hre : 1 - lam / Real.log z ≤ ρ.re) (hright : ρ.re < 1)
    (hheight : Real.log χ.conductor + Real.log (max 1 |ρ.im|) ≤ Real.log z) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK χ.primitiveCharacter ρ.im ≤
      -(Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)) := by
  have hα := source_alpha_ge_half hz (hlam₁.trans (row_basic_certificate r).2.1)
  exact primitive_row_selected_cost r
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one χ hχ)
    χ.primitiveCharacter_isPrimitive hz hlam hlam₁
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero χ hχ (by linarith) hzero)
    hre hright hheight

theorem zeta_row_selected_cost (r : DensityRow) {z lam : ℝ} {ρ : ℂ}
    (hz : 100000000000 ≤ z) (hlam : 0 ≤ lam) (hlam₁ : lam ≤ rowLambda r)
    (hzero : riemannZeta ρ = 0) (hre : 1 - lam / Real.log z ≤ ρ.re) (hright : ρ.re < 1)
    (hheight : Real.log (max 1 |ρ.im|) ≤ Real.log z) :
    let σ := 1 + rowA r / Real.log z
    logKernel σ (stechkinSigma σ) stechkinK (1 : DirichletCharacter ℂ 1) ρ.im ≤
      -(Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)) := by
  dsimp only
  rw [logKernel_eq_dampedLogDeriv]
  simp only [dampedLogDeriv, DirichletCharacter.LFunction_modOne_eq]
  change zetaDamped (1 + rowA r / Real.log z) ρ.im ≤ _
  have hL : 25 ≤ Real.log z := by linarith [source_log_lower hz]
  have hmax := (row_basic_certificate r).2.1
  have hr : 1 / 2 < ρ.re := by
    have hh : lam / Real.log z < 1 / 2 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hxi := (xi_zero_iff_zeta_zero (by linarith : -2 < ρ.re)
    (show ρ ≠ 1 by intro hh; simp [hh] at hright)).mpr hzero
  obtain ⟨p, hp⟩ := BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    differentiable_riemannXi riemannXi_nontrivial
    (show ρ ≠ 0 by intro hh; norm_num [hh] at hr) hxi
  change riemannXiDivisorZeroValue p = ρ at hp
  have hσ := row_sigma_bounds r hz
  have hpair := RealClosure.xi_selected_pair_le p (by simpa [hp] using hr) hσ.1 ρ.im
  have hdom := selected_pair_dominates hσ.1 ⟨by linarith, hright⟩
  rw [hp] at hpair
  have hid := zeta_full_zero_sum_identity hσ.1 ρ.im
  have hg := shiftedGamma_small_sigma hσ.1 hσ.2 ρ.im
  have ht : 1 ≤ |ρ.im| := by simpa [hp] using (xi_zero_height_gt_one p).le
  have hpol := poleDifference_high_nonpos hσ.1 (by linarith) ht
  have hk : 0 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_mem.2]
  have hh := mul_le_mul_of_nonneg_left hheight hk
  have hrec := source_selected_reciprocal r hz hlam hre hright
  have he : -(Real.log z * zeroBudget (rowA r) lam stechkinConductorCoeff (1 / Real.log z)) =
      stechkinConductorCoeff * Real.log z + 0.0755 - Real.log z * (1 / (rowA r + lam)) := by
    unfold zeroBudget
    field_simp
    ring
  rw [he]
  linarith

end LiuWang.Proof.NearOneDensity
