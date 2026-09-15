import LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral.Weight
import LiuWang.Proof.Campaign20260915.Totient.RSTrivialKernel
import LiuWang.Proof.Campaign20260915.Totient.RSParameters

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open LiuWang.Proof.Campaign20260915.Totient
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral

def trivialCoefficient (n : ℕ) : ℝ := 1 / ((2 * n + 2) * (2 * n + 3))

def trivialTailTerm (n : ℕ) (x : ℝ) : ℝ :=
  x⁻¹ ^ (2 * n + 3) * trivialCoefficient n

theorem trivialCoefficient_summable : Summable trivialCoefficient := by
  apply Summable.of_nonneg_of_le (fun n => by unfold trivialCoefficient; positivity)
    (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) _ gammaMellin_weights_summable
  intro n
  apply one_div_le_one_div_of_le (by positivity)
  have hn := Nat.cast_nonneg (α := ℝ) n
  nlinarith

theorem trivialCoefficient_sum_lt :
    (∑' n, trivialCoefficient n) < (31 / 100 : ℝ) := by
  have hs : Summable (fun n : ℕ => 1 / (((n + 8 : ℕ) : ℝ) + 1) ^ 2) :=
    (summable_nat_add_iff 8).mpr gammaMellin_weights_summable
  have hb := ((summable_nat_add_iff 8).mpr trivialCoefficient_summable).tsum_le_tsum
    (g := fun n : ℕ => (1 / 4 : ℝ) * (1 / (((n + 8 : ℕ) : ℝ) + 1) ^ 2))
    (fun n => by
      dsimp [trivialCoefficient]
      rw [one_div_mul_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith)
    (hs.mul_left (1 / 4))
  rw [tsum_mul_left] at hb
  have ht := Complex.tsum_one_div_natCast_add_add_one_sq_le (N := 8) (by omega)
  have he := trivialCoefficient_summable.sum_add_tsum_nat_add 8
  have hf : (∑ n ∈ Finset.range 8, trivialCoefficient n) = (681971 / 2450448 : ℝ) := by
    norm_num [trivialCoefficient, Finset.sum_range_succ]
  rw [hf] at he
  norm_num only [Nat.cast_ofNat] at ht
  linarith

theorem trivialTailTerm_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (trivialTailTerm n) (-(rsTrivialTerm n x / x ^ 2)) x := by
  convert! ((hasDerivAt_inv hx.ne').pow (2 * n + 3)).mul_const
    (trivialCoefficient n) using 1
  simp only [trivialCoefficient, rsTrivialTerm, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega,
    show 2 * n + 3 - 1 = 2 * n + 2 by omega]
  have hn : (2 : ℝ) * n + 3 ≠ 0 := by positivity
  field_simp

theorem trivialTailTerm_tendsto_zero (n : ℕ) :
    Tendsto (trivialTailTerm n) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.pow (2 * n + 3)).mul_const (trivialCoefficient n)
  change Tendsto (fun x : ℝ => x⁻¹ ^ (2 * n + 3) * trivialCoefficient n) atTop (𝓝 0)
  simpa only [zero_pow (by omega : 2 * n + 3 ≠ 0), zero_mul] using h

theorem trivialTerm_div_sq_integrable (n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => rsTrivialTerm n y / y ^ 2) (Ioi x) := by
  have h := integrableOn_Ioi_deriv_of_nonpos'
    (fun y (hy : y ∈ Ici x) => trivialTailTerm_hasDerivAt n (hx.trans_le hy))
    (fun y (hy : y ∈ Ioi x) => neg_nonpos.mpr
      (div_nonneg (rsTrivialTerm_nonneg n (hx.trans hy)) (sq_nonneg y)))
    (trivialTailTerm_tendsto_zero n)
  exact h.neg.congr (Filter.Eventually.of_forall (fun y => neg_neg (rsTrivialTerm n y / y ^ 2)))

theorem trivialTerm_div_sq_integral (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioi x, rsTrivialTerm n y / y ^ 2) = trivialTailTerm n x := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y (hy : y ∈ Ici x) => trivialTailTerm_hasDerivAt n (hx.trans_le hy))
    (trivialTerm_div_sq_integrable n hx).neg (trivialTailTerm_tendsto_zero n)
  rw [integral_neg, zero_sub] at h
  exact neg_injective h

theorem inv_sq_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi x) := by
  simpa using
    (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hx)

theorem trivialKernel_div_sq_integrable {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun y => rsTrivialKernel y / y ^ 2) (Ioi x) := by
  refine ((inv_sq_integrable (by linarith : 0 < x)).const_mul (rsTrivialKernel x)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold rsTrivialKernel; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (rsTrivialKernel_nonneg (hx.trans hy)) (sq_nonneg y)), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right
    (rsTrivialKernel_antitone hx (hx.trans hy) hy.le) (sq_nonneg y)

theorem trivialKernel_div_sq_integral {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, rsTrivialKernel y / y ^ 2) = ∑' n, trivialTailTerm n x := by
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi x))
    (F := fun n y => rsTrivialTerm n y / y ^ 2)
    (f := fun y => rsTrivialKernel y / y ^ 2)
    (fun n y => rsTrivialTerm n x / y ^ 2)
    (fun n => (trivialTerm_div_sq_integrable n (by linarith : 0 < x)).aestronglyMeasurable)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := lt_trans (by linarith : 0 < x) hy
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (rsTrivialTerm_nonneg n hy0) (sq_nonneg y))]
      exact div_le_div_of_nonneg_right
        (rsTrivialTerm_antitone n (by linarith : 0 < x)
          hy0 hy.le) (sq_nonneg y))
    (Filter.Eventually.of_forall (fun y => (rsTrivialTerm_hasSum hx).summable.div_const _))
    (by
      simp_rw [tsum_div_const, (rsTrivialTerm_hasSum hx).tsum_eq, div_eq_mul_inv]
      exact (inv_sq_integrable (by linarith : 0 < x)).const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (rsTrivialTerm_hasSum (hx.trans hy)).div_const _)
  simpa only [trivialTerm_div_sq_integral _ (by linarith : 0 < x)] using h.tsum_eq.symm

theorem trivialTailTerm_bound (n : ℕ) {x : ℝ} (hx : 1 < x) :
    trivialTailTerm n x ≤ x⁻¹ ^ 3 * trivialCoefficient n := by
  unfold trivialTailTerm
  apply mul_le_mul_of_nonneg_right _ (by unfold trivialCoefficient; positivity)
  rw [pow_add]
  apply mul_le_of_le_one_left (by positivity)
  exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hx.le)

theorem trivialTailTerm_summable {x : ℝ} (hx : 1 < x) :
    Summable (fun n => trivialTailTerm n x) :=
  Summable.of_nonneg_of_le (fun n => by unfold trivialTailTerm trivialCoefficient; positivity)
    (fun n => trivialTailTerm_bound n hx) (trivialCoefficient_summable.mul_left _)

theorem trivialKernel_div_sq_integral_lt {x : ℝ} (hx : 1 < x) :
    (∫ y in Ioi x, rsTrivialKernel y / y ^ 2) < (31 / 100 : ℝ) / x ^ 3 := by
  rw [trivialKernel_div_sq_integral hx]
  have h := (trivialTailTerm_summable hx).tsum_le_tsum
    (fun n => trivialTailTerm_bound n hx) (trivialCoefficient_summable.mul_left (x⁻¹ ^ 3))
  rw [tsum_mul_left] at h
  have ht := mul_lt_mul_of_pos_left trivialCoefficient_sum_lt
    (pow_pos (inv_pos.mpr (by linarith : 0 < x)) 3)
  apply h.trans_lt (ht.trans_eq _)
  simp only [inv_pow, div_eq_mul_inv, mul_comm]

#print axioms trivialKernel_div_sq_integral
#print axioms trivialKernel_div_sq_integral_lt

end LiuWang.Proof.Campaign20260915.RSWeightedPsiIntegral
