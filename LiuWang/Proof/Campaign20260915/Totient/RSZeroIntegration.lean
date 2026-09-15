import LiuWang.Proof.Campaign20260915.Totient.RSZeroDifferenceSum
import LiuWang.Proof.ChebyshevBound.IntegratedFormula.ZeroMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rsZeroPrimitive_continuousOn (m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    ContinuousOn (fun x => rsZeroPrimitive m x p) (Ioi 0) := by
  intro x hx
  have hr : riemannXiDivisorZeroValue p + (m : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hh
    have hn := Nat.cast_nonneg (α := ℝ) m
    linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).1]
  exact ((hasDerivAt_ofReal_cpow_const hx.ne' hr).div_const
    (∏ k ∈ Finset.range (m + 1), (riemannXiDivisorZeroValue p + (k : ℂ)))).continuousAt.continuousWithinAt

theorem rsZeroPrimitive_compact_bound (m : ℕ) (p : RiemannXiDivisorZeroIndex)
    {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) :
    ‖rsZeroPrimitive m t p‖ ≤ y ^ (m + 1) * rsZeroMoment m 0 p := by
  have ht0 : 0 < t := by linarith
  have hb : ‖rsZeroPrimitive m t p‖ ≤ t ^ (m + 1) * rsZeroMoment m (Real.log t) p := by
    simpa using rsZeroPrimitive_shift_bound m 0 p ht0 (le_refl (0 : ℝ))
  have he : rsZeroMoment m (Real.log t) p ≤ rsZeroMoment m 0 p := by
    unfold rsZeroMoment
    simp only [mul_zero, Real.exp_zero]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (by linarith [(riemannXiDivisorZeroValue_re_mem_Ioo p).2]) (Real.log_nonneg ht)
  exact hb.trans (mul_le_mul (pow_le_pow_left₀ ht0.le hty _) he
    (by unfold rsZeroMoment; positivity) (pow_nonneg (ht0.le.trans hty) _))

theorem rsZeroSum_continuousOn_Icc {m : ℕ} (hm : 1 ≤ m) {a b : ℝ}
    (ha : 1 ≤ a) :
    ContinuousOn (fun x => ∑' p, rsZeroPrimitive m x p) (Icc a b) := by
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) :=
    fun _ hx => lt_of_lt_of_le (by linarith : 0 < a) hx.1
  apply continuousOn_tsum
    (fun p => (rsZeroPrimitive_continuousOn m p).mono hsub)
    ((rsZeroMoment_summable hm (le_refl (0 : ℝ))).mul_left (b ^ (m + 1)))
  intro p x hx
  exact rsZeroPrimitive_compact_bound m p (ha.trans hx.1) hx.2

theorem rsZeroSum_integral {m : ℕ} (hm : 1 ≤ m) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, ∑' p, rsZeroPrimitive m t p) =
      (∑' p, rsZeroPrimitive (m + 1) b p) -
        ∑' p, rsZeroPrimitive (m + 1) a p := by
  have hmem (t : ℝ) (ht : t ∈ uIcc a b) : 1 ≤ t ∧ t ≤ b := by
    rw [uIcc_of_le hab] at ht
    exact ⟨ha.trans ht.1, ht.2⟩
  have hcont (p : RiemannXiDivisorZeroIndex) :
      ContinuousOn (fun t => rsZeroPrimitive m t p) (uIcc a b) :=
    (rsZeroPrimitive_continuousOn m p).mono (fun t ht => by
      change 0 < t
      linarith [(hmem t ht).1])
  have he (p : RiemannXiDivisorZeroIndex) :
      (∫ t in a..b, rsZeroPrimitive m t p) =
        rsZeroPrimitive (m + 1) b p - rsZeroPrimitive (m + 1) a p :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => rsZeroPrimitive_deriv m p (by linarith [(hmem t ht).1]))
      (hcont p).intervalIntegrable
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (f := fun t => ∑' p, rsZeroPrimitive m t p)
    (fun p _ => b ^ (m + 1) * rsZeroMoment m 0 p)
    (fun p => ((hcont p).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    (fun p => Filter.Eventually.of_forall (fun t ht =>
      rsZeroPrimitive_compact_bound m p
        (hmem t (uIoc_subset_uIcc ht)).1 (hmem t (uIoc_subset_uIcc ht)).2))
    (Filter.Eventually.of_forall (fun _ _ =>
      (rsZeroMoment_summable hm (le_refl (0 : ℝ))).mul_left (b ^ (m + 1))))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t ht =>
      (rsZeroPrimitive_summable hm (hmem t (uIoc_subset_uIcc ht)).1).hasSum))
  rw [← hsum.tsum_eq]
  simp_rw [he]
  exact (rsZeroPrimitive_summable (by omega : 1 ≤ m + 1) (ha.trans hab)).tsum_sub
    (rsZeroPrimitive_summable (by omega : 1 ≤ m + 1) ha)

#print axioms rsZeroPrimitive_continuousOn
#print axioms rsZeroPrimitive_compact_bound
#print axioms rsZeroSum_continuousOn_Icc
#print axioms rsZeroSum_integral

end LiuWang.Proof.Campaign20260915.Totient
