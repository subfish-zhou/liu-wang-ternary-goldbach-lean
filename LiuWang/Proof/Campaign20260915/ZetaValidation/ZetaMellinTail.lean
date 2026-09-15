import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsMellinTailKernel (m : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (-(m : ℝ) * x) / (Real.exp x - 1) : ℝ) : ℂ)

theorem rsMellinTailKernel_hasSum (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (Real.exp (-((n + m + 1 : ℕ) : ℝ) * x) : ℂ))
      (rsMellinTailKernel m x) := by
  have hq0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hq1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := Complex.hasSum_ofReal.mpr ((hasSum_geometric_of_lt_one hq0 hq1).mul_left
    (Real.exp (-((m : ℝ) + 1) * x)))
  convert! h using 1
  · ext n
    apply congrArg Complex.ofReal
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  · unfold rsMellinTailKernel
    apply congrArg Complex.ofReal
    have he : Real.exp (-((m : ℝ) + 1) * x) =
        Real.exp (-(m : ℝ) * x) * Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
    rw [he, Real.exp_neg]
    field_simp

theorem rsMellinTail_mellin (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    mellin (rsMellinTailKernel m) s =
      Gamma s * (riemannZeta s - ∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) := by
  have hsum : Summable (fun n : ℕ => 1 / ((n + m + 1 : ℕ) : ℝ) ^ s.re) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
      (summable_nat_add_iff (m + 1)).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  have hm := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ))
    (p := fun n : ℕ => ((n + m + 1 : ℕ) : ℝ))
    (fun n => Or.inr (by positivity)) (by linarith : 0 < s.re)
    (fun x hx => by simpa using rsMellinTailKernel_hasSum m hx)
    (by simpa using hsum)
  have hbase : HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have hb : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
      simpa using (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    exact hb.hasSum
  have ht := ((hasSum_nat_add_iff' m).mpr hbase).mul_left (Gamma s)
  apply hm.unique
  convert! ht using 1
  ext n
  push_cast
  ring

theorem zeta_eq_sum_add_mellin_tail (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (∑ n ∈ Finset.range m, 1 / (n + 1 : ℂ) ^ s) +
      (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        ((Real.exp (-(m : ℝ) * x) / (Real.exp x - 1) : ℝ) : ℂ)) / Gamma s := by
  have h := rsMellinTail_mellin m hs
  change (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
    ((Real.exp (-(m : ℝ) * x) / (Real.exp x - 1) : ℝ) : ℂ)) = _ at h
  rw [h, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (by linarith))]
  ring

theorem rsMellinTail_integrable {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * rsMellinTailKernel m x) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => x ^ (s.re - 2) * Real.exp (-(m : ℝ) * x))
      (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (by linarith : -1 < s.re - 2) le_rfl (by exact_mod_cast hm : (0 : ℝ) < m)
  apply hg.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hc : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (s - 1)) x :=
      (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hx)).comp continuous_ofReal.continuousAt
    apply ContinuousAt.continuousWithinAt
    apply hc.mul
    unfold rsMellinTailKernel
    apply continuous_ofReal.continuousAt.comp
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hx))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hden : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re,
      rsMellinTailKernel, norm_real, Real.norm_eq_abs, abs_of_pos
        (div_pos (Real.exp_pos _) (by linarith : 0 < Real.exp x - 1))]
    calc
      _ ≤ x ^ (s.re - 1) * (Real.exp (-(m : ℝ) * x) / x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.exp_pos _).le hx0 hden)
          (Real.rpow_nonneg hx0.le _)
      _ = _ := by
        rw [← mul_div_assoc, mul_div_right_comm]
        have hp : x ^ (s.re - 1) / x = x ^ (s.re - 2) := by
          calc
            _ = x ^ (s.re - 1) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_sub hx0]; congr 1; ring
        rw [hp]

end LiuWang.Proof.Campaign20260915.ZetaValidation
