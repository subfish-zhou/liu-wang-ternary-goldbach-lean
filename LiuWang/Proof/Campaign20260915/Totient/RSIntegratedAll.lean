import LiuWang.Proof.Campaign20260915.Totient.RSPsiDifference
import LiuWang.Proof.Campaign20260915.Totient.RSZeroDifferenceSum
import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Difference

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ChebyshevBound.IntegratedFormula
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.Campaign20260915.Totient

theorem rsPsiPrimitive_one_eq_integrated {x : ℝ} (hx : 0 ≤ x) :
    rsPsiPrimitive 1 x = integratedPsi x := by
  classical
  let f (n : ℕ) (t : ℝ) := (Ici (n : ℝ)).indicator
    (fun _ => ArithmeticFunction.vonMangoldt n) t
  have hf (n : ℕ) : Monotone (f n) := by
    intro a b hab
    dsimp [f]
    by_cases ha : a ∈ Ici (n : ℝ)
    · rw [indicator_of_mem ha,
        indicator_of_mem (show b ∈ Ici (n : ℝ) from ha.trans hab)]
    · rw [indicator_of_notMem ha]
      exact indicator_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg) _
  have hsum (t : ℝ) (ht : t ∈ Icc 0 x) :
      Chebyshev.psi t = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n t := by
    rw [Chebyshev.psi]
    have hsub : Finset.Ioc 0 ⌊t⌋₊ ⊆ Finset.Ioc 0 ⌊x⌋₊ :=
      Finset.Ioc_subset_Ioc le_rfl (Nat.floor_le_floor ht.2)
    calc
      _ = ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, f n t := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnT := (Nat.le_floor_iff ht.1).mp (Finset.mem_Ioc.mp hn).2
        exact (indicator_of_mem (show t ∈ Ici (n : ℝ) from hnT)
          (fun _ => ArithmeticFunction.vonMangoldt n)).symm
      _ = _ := Finset.sum_subset hsub (by
        intro n hn hnt
        have hnt' : ¬ (n : ℝ) ≤ t := by
          intro hnT
          exact hnt (Finset.mem_Ioc.mpr
            ⟨(Finset.mem_Ioc.mp hn).1, (Nat.le_floor_iff ht.1).mpr hnT⟩)
        exact indicator_of_notMem (show t ∉ Ici (n : ℝ) from hnt') _)
  have hint (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
      (∫ t in (0 : ℝ)..x, f n t) =
        ArithmeticFunction.vonMangoldt n * (x - n) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2
    have he : Ici (n : ℝ) ∩ Ioc 0 x = Icc (n : ℝ) x := by
      ext t
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor <;> intro ht
      · exact ⟨ht.1, ht.2.2⟩
      · exact ⟨ht.1, hn0.trans_le ht.1, ht.2⟩
    change (∫ t in (0 : ℝ)..x, (Ici (n : ℝ)).indicator
      (fun _ => ArithmeticFunction.vonMangoldt n) t) = _
    rw [intervalIntegral.integral_of_le hx, MeasureTheory.integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, he, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hnx, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  change (∫ t in (0 : ℝ)..x, Chebyshev.psi t) = _
  rw [intervalIntegral.integral_congr (fun t ht => hsum t (by simpa [uIcc_of_le hx] using ht)),
    intervalIntegral.integral_finsetSum (fun n _ => (hf n).intervalIntegrable)]
  exact Finset.sum_congr rfl hint

theorem rsZeroPrimitive_one (x : ℝ) (p : RiemannXiDivisorZeroIndex) :
    rsZeroPrimitive 1 x p = integratedZeroTerm x p := by
  simp [rsZeroPrimitive, integratedZeroTerm, Finset.prod_range_succ]

theorem rs_integrated_formula_all {x : ℝ} (hx : 1 < x) :
    (integratedPsi x : ℂ) =
      ((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) * ((x : ℂ) - 1) +
      ((x : ℂ) - 1) ^ 2 / 2 -
      ((∑' p, integratedZeroTerm x p) - ∑' p, integratedZeroTerm 1 p) +
      gammaCorrection x := by
  have hs : Summable (integratedZeroTerm x) := by
    rw [← show rsZeroPrimitive 1 x = integratedZeroTerm x from funext (rsZeroPrimitive_one x)]
    exact rsZeroPrimitive_summable (by omega : 1 ≤ 1) hx.le
  rw [integratedPsi_eq_spectral hx]
  unfold spectralMellin
  rw [mul_add, mul_add, mul_sub, mul_left_comm _ _ (triangle x⁻¹),
    scaled_triangle_inverse hx.le, scaled_pole_inverse hx.le, zeroSum_at_inverse hx.le,
    hs.tsum_sub integratedZeroTerm_summable_one]
  unfold gammaCorrection
  ring

theorem rsPsiPrimitive_one_spectral {x : ℝ} (hx : 1 < x) :
    (rsPsiPrimitive 1 x : ℂ) =
      ((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) * ((x : ℂ) - 1) +
      ((x : ℂ) - 1) ^ 2 / 2 -
      ((∑' p, rsZeroPrimitive 1 x p) - ∑' p, rsZeroPrimitive 1 1 p) +
      gammaCorrection x := by
  rw [rsPsiPrimitive_one_eq_integrated (by linarith)]
  simpa only [rsZeroPrimitive_one] using rs_integrated_formula_all hx

#print axioms rsPsiPrimitive_one_eq_integrated
#print axioms rsZeroPrimitive_one
#print axioms rs_integrated_formula_all
#print axioms rsPsiPrimitive_one_spectral

end LiuWang.Proof.Campaign20260915.Totient
