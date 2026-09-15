import LiuWang.Proof.SingularIntegral.Consumer

/-!
# Simple J bounds and the actual two-sided integral tail

The reciprocal estimate is used only away from zero. Specializing the
accepted fixed-parameter decay producer at `rho = 1` pays both bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Interval
open AnalyticNumberTheory.LargeSieve LiuWang.Proof.Interfaces
open LiuWang.Proof.SingularIntegral

namespace LiuWang.Proof.SingularSeries

theorem weightMass_one (N : ℕ) : weightMass N 1 = 0.999 * (N : ℝ) := by
  simp [weightMass, sourceWindowLower]
  ring

theorem weightVariation_one (N : ℕ) : weightVariation N 1 = 1 / Real.pi := by
  simp [weightVariation]
  ring

theorem J_norm_le_length (N : ℕ) (eta : ℝ) : ‖J N eta‖ ≤ 0.999 * (N : ℝ) := by
  simpa only [Jrho_one_eq_J, weightMass_one] using Jrho_norm_le_mass N 1 eta

theorem J_abs_mul_norm_le {N : ℕ} (hN : 0 < N) (eta : ℝ) :
    |eta| * ‖J N eta‖ ≤ 1 / Real.pi := by
  simpa only [Jrho_one_eq_J, weightVariation_one] using
    Jrho_abs_mul_norm_le_variation hN 1 eta

theorem J_norm_le_reciprocal {N : ℕ} (hN : 0 < N) {eta : ℝ} (heta : eta ≠ 0) :
    ‖J N eta‖ ≤ 1 / (Real.pi * |eta|) := by
  have h : ‖J N eta‖ ≤ (1 / Real.pi) / |eta| :=
    (le_div_iff₀ (abs_pos.mpr heta)).mpr
    (by simpa [mul_comm] using J_abs_mul_norm_le hN eta)
  simpa only [div_div] using h

theorem J_norm_le_min {N : ℕ} (hN : 0 < N) {eta : ℝ} (heta : eta ≠ 0) :
    ‖J N eta‖ ≤ min (0.999 * (N : ℝ)) (1 / (Real.pi * |eta|)) :=
  le_min (J_norm_le_length N eta) (J_norm_le_reciprocal hN heta)

theorem J_zero (N : ℕ) : J N 0 = (0.999 * (N : ℝ) : ℝ) := by
  simp [J, charReal, sourceWindowLower]
  ring

def cubeIntegrand (N : ℕ) (eta : ℝ) : ℂ :=
  J N eta ^ 3 * charReal (-(N : ℝ) * eta)

theorem cubeIntegrand_integrable {N : ℕ} (hN : 0 < N) :
    Integrable (cubeIntegrand N) := J_cube_integrable hN

theorem cubeIntegrand_norm_le {N : ℕ} (hN : 0 < N) {eta : ℝ} (heta : eta ≠ 0) :
    ‖cubeIntegrand N eta‖ ≤ (1 / Real.pi ^ 3) / |eta| ^ 3 := by
  simp only [cubeIntegrand, norm_mul, norm_pow, charReal_norm, mul_one]
  have h := pow_le_pow_left₀ (norm_nonneg _) (J_norm_le_reciprocal hN heta) 3
  simpa only [div_pow, one_pow, mul_pow, div_div] using h

theorem norm_integral_Ioi_le_inv_cube {f : ℝ → ℂ} (hf : Integrable f)
    {delta C : ℝ} (hd : 0 < delta)
    (hbound : ∀ x, delta < x → ‖f x‖ ≤ C / x ^ 3) :
    ‖∫ x in Ioi delta, f x‖ ≤ C / (2 * delta ^ 2) := by
  have hg : IntegrableOn (fun x : ℝ => C * x ^ (-3 : ℝ)) (Ioi delta) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hd).const_mul C
  calc
    _ ≤ ∫ x in Ioi delta, ‖f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi delta, C * x ^ (-3 : ℝ) := by
      apply setIntegral_mono_on hf.norm.integrableOn hg measurableSet_Ioi
      intro x hx
      have hx0 : 0 ≤ x := (hd.trans hx).le
      simpa only [show (-3 : ℝ) = -(3 : ℝ) by norm_num,
        Real.rpow_neg hx0, Real.rpow_ofNat, div_eq_mul_inv] using hbound x hx
    _ = C / (2 * delta ^ 2) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hd]
      norm_num
      ring

theorem integral_sub_interval_eq_tails {f : ℝ → ℂ} (hf : Integrable f)
    {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ x : ℝ, f x) - (∫ x in -delta..delta, f x) =
      (∫ x in Iic (-delta), f x) + ∫ x in Ioi delta, f x := by
  have he : (Ioc (-delta) delta)ᶜ = Iic (-delta) ∪ Ioi delta := by
    ext x
    simp only [mem_compl_iff, mem_Ioc, mem_union, mem_Iic, mem_Ioi, not_and_or, not_lt, not_le]
  have hdis : Disjoint (Iic (-delta)) (Ioi delta) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [mem_Iic, mem_Ioi] at hx hy
    linarith
  have h := integral_add_compl (s := Ioc (-delta) delta) measurableSet_Ioc hf
  rw [he, setIntegral_union hdis measurableSet_Ioi hf.integrableOn hf.integrableOn] at h
  rw [intervalIntegral.integral_of_le (by linarith : -delta ≤ delta)]
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

theorem cube_integral_tail_bound {N : ℕ} (hN : 0 < N) {delta : ℝ} (hd : 0 < delta) :
    ‖(∫ eta : ℝ, cubeIntegrand N eta) -
      (∫ eta in -delta..delta, cubeIntegrand N eta)‖ ≤
        1 / (Real.pi ^ 3 * delta ^ 2) := by
  have hf := cubeIntegrand_integrable hN
  have hright := norm_integral_Ioi_le_inv_cube hf hd (C := 1 / Real.pi ^ 3) (by
    intro x hx
    simpa only [abs_of_pos (hd.trans hx)] using
      cubeIntegrand_norm_le hN (hd.trans hx).ne')
  have hleft := norm_integral_Ioi_le_inv_cube hf.comp_neg hd (C := 1 / Real.pi ^ 3) (by
    intro x hx
    simpa only [abs_neg, abs_of_pos (hd.trans hx)] using
      cubeIntegrand_norm_le hN (neg_ne_zero.mpr (hd.trans hx).ne'))
  rw [integral_comp_neg_Ioi] at hleft
  rw [integral_sub_interval_eq_tails hf hd.le]
  exact (norm_add_le _ _).trans (by
    calc
      _ ≤ (1 / Real.pi ^ 3) / (2 * delta ^ 2) +
          (1 / Real.pi ^ 3) / (2 * delta ^ 2) := add_le_add hleft hright
      _ = _ := by ring)

theorem cube_integral_truncation {N : ℕ} (hN : 0 < N) {delta : ℝ} (hd : 0 < delta) :
    ‖(N : ℂ) ^ 2 * ((0.997 : ℂ) ^ 2 / 2) -
      (∫ eta in -delta..delta, cubeIntegrand N eta)‖ ≤
        1 / (Real.pi ^ 3 * delta ^ 2) := by
  simpa only [cubeIntegrand, integral_J_cube hN] using cube_integral_tail_bound hN hd

end LiuWang.Proof.SingularSeries
